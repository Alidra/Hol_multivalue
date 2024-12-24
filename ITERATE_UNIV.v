Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_UNIV_term_abbrevs.
Require Import ITERATE_SUPERSET_spec.
Require Import SUBSET_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem6962210 {A B : Type'} (op : type1400 B) : term0 A B op.
Proof. exact (@lem6016892 A B op). Qed.
Lemma lem6962211 {A B : Type'} (op : type1400 B) : (term0 A B op) = (term1 A B op).
Proof. exact (eq_refl (term0 A B op)). Qed.
Lemma lem6962237 {_83095 : Type'} : term2 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem6962238 {_83095 : Type'} (p : _83095 -> Prop) : term3 _83095 p.
Proof. exact (@lem6962237 _83095 p). Qed.
Lemma lem6962239 {_83095 : Type'} (p : _83095 -> Prop) : (term3 _83095 p) = (term4 _83095 p).
Proof. exact (eq_refl (term3 _83095 p)). Qed.
Lemma lem6962240 {_83095 : Type'} (p : _83095 -> Prop) : term4 _83095 p.
Proof. exact (EQ_MP (@lem6962239 _83095 p) (@lem6962238 _83095 p)). Qed.
Lemma lem6962241 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term5 _83095 p x.
Proof. exact (@lem6962240 _83095 p x). Qed.
Lemma lem6962242 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term5 _83095 p x) = ((term6 _83095 x p) = (p x)).
Proof. exact (eq_refl (term5 _83095 p x)). Qed.
Lemma lem6962251 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem6962252 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem6962253 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem6962252 A s) (@lem6962251 A s)). Qed.
Lemma lem6962254 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem6962253 A s t). Qed.
Lemma lem6962255 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = ((@SUBSET A s t) = (term10 A s t)).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem6962257 {A B : Type'} (s : A -> Prop) : term11 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem6962258 {A B : Type'} (s : A -> Prop) : (term11 A B s) = (term12 A B s).
Proof. exact (eq_refl (term11 A B s)). Qed.
Lemma lem6962259 {A B : Type'} (s : A -> Prop) : term12 A B s.
Proof. exact (EQ_MP (@lem6962258 A B s) (@lem6962257 A B s)). Qed.
Lemma lem6962260 {A B : Type'} (s : A -> Prop) (f : A -> B) : term13 A B s f.
Proof. exact (@lem6962259 A B s f). Qed.
Lemma lem6962261 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term13 A B s f) = (term14 A B s f).
Proof. exact (eq_refl (term13 A B s f)). Qed.
Lemma lem6962262 {A B : Type'} (s : A -> Prop) (f : A -> B) : term14 A B s f.
Proof. exact (EQ_MP (@lem6962261 A B s f) (@lem6962260 A B s f)). Qed.
Lemma lem6962263 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term15 A B s f op.
Proof. exact (@lem6962262 A B s f op). Qed.
Lemma lem6962264 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term15 A B s f op) = ((@support A B op f s) = (term16 A B s f op)).
Proof. exact (eq_refl (term15 A B s f op)). Qed.
Lemma lem6962283 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem6962255 A s t) (@lem6962254 A s t)). Qed.
Lemma lem6962284 {_127692 : Type'} (s : _127692 -> Prop) (t : _127692 -> Prop) : (@SUBSET _127692 s t) = (term10 _127692 s t).
Proof. exact (@lem6962283 _127692 s t). Qed.
Lemma lem6962285 {_127673 _127692 : Type'} (op : type1400 _127673) (f : _127692 -> _127673) (s : _127692 -> Prop) : (term17 _127673 _127692 op f s) = (term18 _127673 _127692 op f s).
Proof. exact (@lem6962284 _127692 (@support _127692 _127673 op f (@UNIV _127692)) s). Qed.
Lemma lem6962293 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term16 A B s f op).
Proof. exact (EQ_MP (@lem6962264 A B s f op) (@lem6962263 A B s f op)). Qed.
Lemma lem6962294 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (@support _127692 _127673 op f s) = (term19 _127673 _127692 s f op).
Proof. exact (@lem6962293 _127692 _127673 s f op). Qed.
Lemma lem6962295 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) : (@support _127692 _127673 op f (@UNIV _127692)) = (term20 _127673 _127692 f op).
Proof. exact (@lem6962294 _127673 _127692 (@UNIV _127692) f op). Qed.
Lemma lem6962304 {_127692 : Type'} (x : _127692) : (@IN _127692 x) = (@IN _127692 x).
Proof. exact (eq_refl (@IN _127692 x)). Qed.
Lemma lem6962305 {_127673 _127692 : Type'} (x : _127692) (f : _127692 -> _127673) (op : type1400 _127673) : (term21 _127673 _127692 x op f) = (term22 _127673 _127692 x f op).
Proof. exact (MK_COMB (@lem6962304 _127692 x) (@lem6962295 _127673 _127692 f op)). Qed.
Lemma lem6962307 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term6 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem6962242 _83095 p x) (@lem6962241 _83095 p x)). Qed.
Lemma lem6962308 {_127692 : Type'} (p : _127692 -> Prop) (x : _127692) : (term6 _127692 x p) = (p x).
Proof. exact (@lem6962307 _127692 p x). Qed.
Lemma lem6962309 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (x : _127692) : (term23 _127673 _127692 x f op) = (term24 _127673 _127692 f op x).
Proof. exact (@lem6962308 _127692 (term25 _127673 _127692 f op) x). Qed.
Lemma lem6962310 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term24 _127673 _127692 f op x) = (term26 _127673 _127692 f x op).
Proof. exact (eq_refl (term24 _127673 _127692 f op x)). Qed.
Lemma lem6962311 {_127692 : Type'} (GEN_PVAR_237 : _127692) : (@SETSPEC _127692 GEN_PVAR_237) = (@SETSPEC _127692 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _127692 GEN_PVAR_237)). Qed.
Lemma lem6962312 {_127673 _127692 : Type'} (GEN_PVAR_237 : _127692) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term27 _127673 _127692 GEN_PVAR_237 f op x) = (term28 _127673 _127692 GEN_PVAR_237 f x op).
Proof. exact (MK_COMB (@lem6962311 _127692 GEN_PVAR_237) (@lem6962310 _127673 _127692 f x op)). Qed.
Lemma lem6962313 {_127692 : Type'} (x : _127692) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6962314 {_127673 _127692 : Type'} (GEN_PVAR_237 : _127692) (f : _127692 -> _127673) (op : type1400 _127673) (x : _127692) : (term29 _127673 _127692 GEN_PVAR_237 f op x) = (term30 _127673 _127692 GEN_PVAR_237 f op x).
Proof. exact (MK_COMB (@lem6962312 _127673 _127692 GEN_PVAR_237 f x op) (@lem6962313 _127692 x)). Qed.
Lemma lem6962315 {_127673 _127692 : Type'} (GEN_PVAR_237 : _127692) (f : _127692 -> _127673) (op : type1400 _127673) : (term31 _127673 _127692 GEN_PVAR_237 f op) = (term32 _127673 _127692 GEN_PVAR_237 f op).
Proof. exact (fun_ext (fun x : _127692 => @lem6962314 _127673 _127692 GEN_PVAR_237 f op x)). Qed.
Lemma lem6962316 {_127692 : Type'} : (@ex _127692) = (@ex _127692).
Proof. exact (eq_refl (@ex _127692)). Qed.
Lemma lem6962317 {_127673 _127692 : Type'} (GEN_PVAR_237 : _127692) (f : _127692 -> _127673) (op : type1400 _127673) : (term33 _127673 _127692 GEN_PVAR_237 f op) = (term34 _127673 _127692 GEN_PVAR_237 f op).
Proof. exact (MK_COMB (@lem6962316 _127692) (@lem6962315 _127673 _127692 GEN_PVAR_237 f op)). Qed.
Lemma lem6962318 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) : (term35 _127673 _127692 f op) = (term36 _127673 _127692 f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _127692 => @lem6962317 _127673 _127692 GEN_PVAR_237 f op)). Qed.
Lemma lem6962319 {_127692 : Type'} : (@GSPEC _127692) = (@GSPEC _127692).
Proof. exact (eq_refl (@GSPEC _127692)). Qed.
Lemma lem6962320 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) : (term37 _127673 _127692 f op) = (term20 _127673 _127692 f op).
Proof. exact (MK_COMB (@lem6962319 _127692) (@lem6962318 _127673 _127692 f op)). Qed.
Lemma lem6962321 {_127692 : Type'} (x : _127692) : (@IN _127692 x) = (@IN _127692 x).
Proof. exact (eq_refl (@IN _127692 x)). Qed.
Lemma lem6962322 {_127673 _127692 : Type'} (x : _127692) (f : _127692 -> _127673) (op : type1400 _127673) : (term23 _127673 _127692 x f op) = (term22 _127673 _127692 x f op).
Proof. exact (MK_COMB (@lem6962321 _127692 x) (@lem6962320 _127673 _127692 f op)). Qed.
Lemma lem6962323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6962324 {_127673 _127692 : Type'} (x : _127692) (f : _127692 -> _127673) (op : type1400 _127673) : (term38 _127673 _127692 x f op) = (term39 _127673 _127692 x f op).
Proof. exact (MK_COMB (@lem6962323) (@lem6962322 _127673 _127692 x f op)). Qed.
Lemma lem6962325 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term24 _127673 _127692 f op x) = (term26 _127673 _127692 f x op).
Proof. exact (eq_refl (term24 _127673 _127692 f op x)). Qed.
Lemma lem6962326 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : ((term23 _127673 _127692 x f op) = (term24 _127673 _127692 f op x)) = ((term22 _127673 _127692 x f op) = (term26 _127673 _127692 f x op)).
Proof. exact (MK_COMB (@lem6962324 _127673 _127692 x f op) (@lem6962325 _127673 _127692 f x op)). Qed.
Lemma lem6962327 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term22 _127673 _127692 x f op) = (term26 _127673 _127692 f x op).
Proof. exact (EQ_MP (@lem6962326 _127673 _127692 f x op) (@lem6962309 _127673 _127692 f op x)). Qed.
Lemma lem6962332 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term21 _127673 _127692 x op f) = (term26 _127673 _127692 f x op).
Proof. exact (TRANS (@lem6962305 _127673 _127692 x f op) (@lem6962327 _127673 _127692 f x op)). Qed.
Lemma lem6962333 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6962334 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term40 _127673 _127692 x op f) = (term41 _127673 _127692 f x op).
Proof. exact (MK_COMB (@lem6962333) (@lem6962332 _127673 _127692 f x op)). Qed.
Lemma lem6962335 {_127692 : Type'} (x : _127692) (s : _127692 -> Prop) : (@IN _127692 x s) = (@IN _127692 x s).
Proof. exact (eq_refl (@IN _127692 x s)). Qed.
Lemma lem6962336 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (x : _127692) (s : _127692 -> Prop) : (term42 _127673 _127692 op f x s) = (term43 _127673 _127692 f op x s).
Proof. exact (MK_COMB (@lem6962334 _127673 _127692 f x op) (@lem6962335 _127692 x s)). Qed.
Lemma lem6962339 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term44 _127673 _127692 op f s) = (term45 _127673 _127692 f op s).
Proof. exact (fun_ext (fun x : _127692 => @lem6962336 _127673 _127692 f op x s)). Qed.
Lemma lem6962340 {_127692 : Type'} : (@all _127692) = (@all _127692).
Proof. exact (eq_refl (@all _127692)). Qed.
Lemma lem6962341 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term18 _127673 _127692 op f s) = (term46 _127673 _127692 f op s).
Proof. exact (MK_COMB (@lem6962340 _127692) (@lem6962339 _127673 _127692 f op s)). Qed.
Lemma lem6962346 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term17 _127673 _127692 op f s) = (term46 _127673 _127692 f op s).
Proof. exact (TRANS (@lem6962285 _127673 _127692 op f s) (@lem6962341 _127673 _127692 f op s)). Qed.
Lemma lem6962347 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6962348 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term47 _127673 _127692 op f s) = (term48 _127673 _127692 f op s).
Proof. exact (MK_COMB (@lem6962347) (@lem6962346 _127673 _127692 f op s)). Qed.
Lemma lem6962351 {_127673 _127692 : Type'} (s : _127692 -> Prop) (op : type1400 _127673) (f : _127692 -> _127673) : ((@iterate _127673 _127692 op s f) = (@iterate _127673 _127692 op (@UNIV _127692) f)) = ((@iterate _127673 _127692 op s f) = (@iterate _127673 _127692 op (@UNIV _127692) f)).
Proof. exact (eq_refl ((@iterate _127673 _127692 op s f) = (@iterate _127673 _127692 op (@UNIV _127692) f))). Qed.
Lemma lem6962352 {_127673 _127692 : Type'} (s : _127692 -> Prop) (op : type1400 _127673) (f : _127692 -> _127673) : (term49 _127673 _127692 s op f) = (term50 _127673 _127692 s op f).
Proof. exact (MK_COMB (@lem6962348 _127673 _127692 f op s) (@lem6962351 _127673 _127692 s op f)). Qed.
Lemma lem6962355 {_127673 _127692 : Type'} (op : type1400 _127673) (f : _127692 -> _127673) : (term51 _127673 _127692 op f) = (term52 _127673 _127692 op f).
Proof. exact (fun_ext (fun s : _127692 -> Prop => @lem6962352 _127673 _127692 s op f)). Qed.
Lemma lem6962356 {_127692 : Type'} : (@all (_127692 -> Prop)) = (@all (_127692 -> Prop)).
Proof. exact (eq_refl (@all (_127692 -> Prop))). Qed.
Lemma lem6962357 {_127673 _127692 : Type'} (op : type1400 _127673) (f : _127692 -> _127673) : (term53 _127673 _127692 op f) = (term54 _127673 _127692 op f).
Proof. exact (MK_COMB (@lem6962356 _127692) (@lem6962355 _127673 _127692 op f)). Qed.
Lemma lem6962362 {_127673 _127692 : Type'} (op : type1400 _127673) : (term55 _127673 _127692 op) = (term56 _127673 _127692 op).
Proof. exact (fun_ext (fun f : _127692 -> _127673 => @lem6962357 _127673 _127692 op f)). Qed.
Lemma lem6962363 {_127673 _127692 : Type'} : (@all (_127692 -> _127673)) = (@all (_127692 -> _127673)).
Proof. exact (eq_refl (@all (_127692 -> _127673))). Qed.
Lemma lem6962364 {_127673 _127692 : Type'} (op : type1400 _127673) : (term57 _127673 _127692 op) = (term58 _127673 _127692 op).
Proof. exact (MK_COMB (@lem6962363 _127673 _127692) (@lem6962362 _127673 _127692 op)). Qed.
Lemma lem6962369 {_127673 : Type'} (op : type1400 _127673) : (term59 _127673 op) = (term59 _127673 op).
Proof. exact (eq_refl (term59 _127673 op)). Qed.
Lemma lem6962370 {_127673 _127692 : Type'} (op : type1400 _127673) : (term60 _127673 _127692 op) = (term61 _127673 _127692 op).
Proof. exact (MK_COMB (@lem6962369 _127673 op) (@lem6962364 _127673 _127692 op)). Qed.
Lemma lem6962373 {_127673 _127692 : Type'} : (term62 _127673 _127692) = (term63 _127673 _127692).
Proof. exact (fun_ext (fun op : type1400 _127673 => @lem6962370 _127673 _127692 op)). Qed.
Lemma lem6962374 {_127673 : Type'} : (@all (_127673 -> _127673 -> _127673)) = (@all (_127673 -> _127673 -> _127673)).
Proof. exact (eq_refl (@all (_127673 -> _127673 -> _127673))). Qed.
Lemma lem6962375 {_127673 _127692 : Type'} : (term64 _127673 _127692) = (term65 _127673 _127692).
Proof. exact (MK_COMB (@lem6962374 _127673) (@lem6962373 _127673 _127692)). Qed.
Lemma lem6962380 {_127673 _127692 : Type'} : (term65 _127673 _127692) = (term64 _127673 _127692).
Proof. exact (SYM (@lem6962375 _127673 _127692)). Qed.
Lemma lem6962381 {_127673 : Type'} (op : type1400 _127673) (h1 : @monoidal _127673 op) : @monoidal _127673 op.
Proof. exact (h1). Qed.
Lemma lem6962382 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (h1 : term46 _127673 _127692 f op s) : term46 _127673 _127692 f op s.
Proof. exact (h1). Qed.
Lemma lem6962383 {_127673 _127692 : Type'} (s : _127692 -> Prop) (op : type1400 _127673) (f : _127692 -> _127673) (h1 : (@iterate _127673 _127692 op s f) = (@iterate _127673 _127692 op (@UNIV _127692) f)) : (@iterate _127673 _127692 op s f) = (@iterate _127673 _127692 op (@UNIV _127692) f).
Proof. exact (h1). Qed.
Lemma lem6962384 {_127673 _127692 : Type'} (s : _127692 -> Prop) (op : type1400 _127673) (f : _127692 -> _127673) (h1 : (@iterate _127673 _127692 op s f) = (@iterate _127673 _127692 op (@UNIV _127692) f)) : (@iterate _127673 _127692 op (@UNIV _127692) f) = (@iterate _127673 _127692 op s f).
Proof. exact (SYM (@lem6962383 _127673 _127692 s op f h1)). Qed.
Lemma lem6962385 {_127673 _127692 : Type'} (op : type1400 _127673) (s : _127692 -> Prop) (f : _127692 -> _127673) (h1 : (@iterate _127673 _127692 op (@UNIV _127692) f) = (@iterate _127673 _127692 op s f)) : (@iterate _127673 _127692 op (@UNIV _127692) f) = (@iterate _127673 _127692 op s f).
Proof. exact (h1). Qed.
Lemma lem6962386 {_127673 _127692 : Type'} (op : type1400 _127673) (s : _127692 -> Prop) (f : _127692 -> _127673) (h1 : (@iterate _127673 _127692 op (@UNIV _127692) f) = (@iterate _127673 _127692 op s f)) : (@iterate _127673 _127692 op s f) = (@iterate _127673 _127692 op (@UNIV _127692) f).
Proof. exact (SYM (@lem6962385 _127673 _127692 op s f h1)). Qed.
Lemma lem6962387 {_127673 _127692 : Type'} (op : type1400 _127673) (s : _127692 -> Prop) (f : _127692 -> _127673) : ((@iterate _127673 _127692 op s f) = (@iterate _127673 _127692 op (@UNIV _127692) f)) = ((@iterate _127673 _127692 op (@UNIV _127692) f) = (@iterate _127673 _127692 op s f)).
Proof. exact (prop_ext (fun h1 : (@iterate _127673 _127692 op s f) = (@iterate _127673 _127692 op (@UNIV _127692) f) => @lem6962384 _127673 _127692 s op f h1) (fun h1 : (@iterate _127673 _127692 op (@UNIV _127692) f) = (@iterate _127673 _127692 op s f) => @lem6962386 _127673 _127692 op s f h1)). Qed.
Lemma lem6962388 {_127673 _127692 : Type'} (s : _127692 -> Prop) (op : type1400 _127673) (f : _127692 -> _127673) : ((@iterate _127673 _127692 op (@UNIV _127692) f) = (@iterate _127673 _127692 op s f)) = ((@iterate _127673 _127692 op s f) = (@iterate _127673 _127692 op (@UNIV _127692) f)).
Proof. exact (SYM (@lem6962387 _127673 _127692 op s f)). Qed.
Lemma lem6962392 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (EQ_MP (@lem6962211 A B op) (@lem6962210 A B op)). Qed.
Lemma lem6962393 {_127673 A : Type'} (op : type1400 _127673) : term66 _127673 A op.
Proof. exact (@lem6962392 A _127673 op). Qed.
Lemma lem6962394 {_127673 A : Type'} (op : type1400 _127673) (h1 : @monoidal _127673 op) : term67 _127673 A op.
Proof. exact (@lem6962393 _127673 A op (@lem6962381 _127673 op h1)). Qed.
Lemma lem6962395 {_127673 A : Type'} (op : type1400 _127673) (h1 : term67 _127673 A op) : term67 _127673 A op.
Proof. exact (h1). Qed.
Lemma lem6962396 {_127673 A : Type'} (f : A -> _127673) (op : type1400 _127673) (h1 : term67 _127673 A op) : term68 _127673 A op f.
Proof. exact (@lem6962395 _127673 A op h1 f). Qed.
Lemma lem6962397 {_127673 A : Type'} (op : type1400 _127673) (f : A -> _127673) : (term68 _127673 A op f) = (term69 _127673 A op f).
Proof. exact (eq_refl (term68 _127673 A op f)). Qed.
Lemma lem6962398 {_127673 A : Type'} (f : A -> _127673) (op : type1400 _127673) (h1 : term67 _127673 A op) : term69 _127673 A op f.
Proof. exact (EQ_MP (@lem6962397 _127673 A op f) (@lem6962396 _127673 A f op h1)). Qed.
Lemma lem6962399 {_127673 A : Type'} (f : A -> _127673) (u : A -> Prop) (op : type1400 _127673) (h1 : term67 _127673 A op) : term70 _127673 A op f u.
Proof. exact (@lem6962398 _127673 A f op h1 u). Qed.
Lemma lem6962400 {_127673 A : Type'} (op : type1400 _127673) (u : A -> Prop) (f : A -> _127673) : (term70 _127673 A op f u) = (term71 _127673 A op u f).
Proof. exact (eq_refl (term70 _127673 A op f u)). Qed.
Lemma lem6962401 {_127673 A : Type'} (u : A -> Prop) (f : A -> _127673) (op : type1400 _127673) (h1 : term67 _127673 A op) : term71 _127673 A op u f.
Proof. exact (EQ_MP (@lem6962400 _127673 A op u f) (@lem6962399 _127673 A f u op h1)). Qed.
Lemma lem6962402 {_127673 A : Type'} (u : A -> Prop) (f : A -> _127673) (v : A -> Prop) (op : type1400 _127673) (h1 : term67 _127673 A op) : term72 _127673 A op u f v.
Proof. exact (@lem6962401 _127673 A u f op h1 v). Qed.
Lemma lem6962403 {_127673 A : Type'} (v : A -> Prop) (op : type1400 _127673) (u : A -> Prop) (f : A -> _127673) : (term72 _127673 A op u f v) = (term73 _127673 A v op u f).
Proof. exact (eq_refl (term72 _127673 A op u f v)). Qed.
Lemma lem6962404 {_127673 A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> _127673) (op : type1400 _127673) (h1 : term67 _127673 A op) : term73 _127673 A v op u f.
Proof. exact (EQ_MP (@lem6962403 _127673 A v op u f) (@lem6962402 _127673 A u f v op h1)). Qed.
Lemma lem6962405 {_127673 A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> _127673) (op : type1400 _127673) (h1 : term74 _127673 A v u f op) : term74 _127673 A v u f op.
Proof. exact (h1). Qed.
Lemma lem6962406 {_127673 A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> _127673) (op : type1400 _127673) (h1 : term67 _127673 A op) (h2 : term74 _127673 A v u f op) : (@iterate _127673 A op v f) = (@iterate _127673 A op u f).
Proof. exact (@lem6962404 _127673 A v u f op h1 (@lem6962405 _127673 A v u f op h2)). Qed.
Lemma lem6962407 {_127673 A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> _127673) (op : type1400 _127673) (h1 : term74 _127673 A v u f op) : term75 _127673 A v op u f.
Proof. exact (fun h0 : term67 _127673 A op => @lem6962406 _127673 A v u f op h0 h1). Qed.
Lemma lem6962408 {_127673 A : Type'} (op : type1400 _127673) (h1 : term67 _127673 A op) : term67 _127673 A op.
Proof. exact (h1). Qed.
Lemma lem6962409 {_127673 A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> _127673) (op : type1400 _127673) (h1 : term67 _127673 A op) (h2 : term74 _127673 A v u f op) : (@iterate _127673 A op v f) = (@iterate _127673 A op u f).
Proof. exact (@lem6962407 _127673 A v u f op h2 (@lem6962408 _127673 A op h1)). Qed.
Lemma lem6962410 {_127673 A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> _127673) (op : type1400 _127673) (h1 : term67 _127673 A op) : term73 _127673 A v op u f.
Proof. exact (fun h0 : term74 _127673 A v u f op => @lem6962409 _127673 A v u f op h1 h0). Qed.
Lemma lem6962411 {_127673 A : Type'} (v : A -> Prop) (u : A -> Prop) (op : type1400 _127673) (h1 : term67 _127673 A op) : term76 _127673 A v op u.
Proof. exact (fun f : A -> _127673 => @lem6962410 _127673 A v u f op h1). Qed.
Lemma lem6962412 {_127673 A : Type'} (v : A -> Prop) (op : type1400 _127673) (h1 : term67 _127673 A op) : term77 _127673 A v op.
Proof. exact (fun u : A -> Prop => @lem6962411 _127673 A v u op h1). Qed.
Lemma lem6962413 {_127673 A : Type'} (op : type1400 _127673) (h1 : term67 _127673 A op) : term78 _127673 A op.
Proof. exact (fun v : A -> Prop => @lem6962412 _127673 A v op h1). Qed.
Lemma lem6962414 {_127673 A : Type'} (op : type1400 _127673) : term79 _127673 A op.
Proof. exact (fun h0 : term67 _127673 A op => @lem6962413 _127673 A op h0). Qed.
Lemma lem6962415 {_127673 A : Type'} (op : type1400 _127673) (h1 : @monoidal _127673 op) : term78 _127673 A op.
Proof. exact (@lem6962414 _127673 A op (@lem6962394 _127673 A op h1)). Qed.
Lemma lem6962416 {_127673 A : Type'} (v : A -> Prop) (op : type1400 _127673) (h1 : @monoidal _127673 op) : term80 _127673 A op v.
Proof. exact (@lem6962415 _127673 A op h1 v). Qed.
Lemma lem6962417 {_127673 A : Type'} (v : A -> Prop) (op : type1400 _127673) : (term80 _127673 A op v) = (term77 _127673 A v op).
Proof. exact (eq_refl (term80 _127673 A op v)). Qed.
Lemma lem6962418 {_127673 A : Type'} (v : A -> Prop) (op : type1400 _127673) (h1 : @monoidal _127673 op) : term77 _127673 A v op.
Proof. exact (EQ_MP (@lem6962417 _127673 A v op) (@lem6962416 _127673 A v op h1)). Qed.
Lemma lem6962419 {_127673 A : Type'} (v : A -> Prop) (u : A -> Prop) (op : type1400 _127673) (h1 : @monoidal _127673 op) : term81 _127673 A v op u.
Proof. exact (@lem6962418 _127673 A v op h1 u). Qed.
Lemma lem6962420 {_127673 A : Type'} (v : A -> Prop) (op : type1400 _127673) (u : A -> Prop) : (term81 _127673 A v op u) = (term76 _127673 A v op u).
Proof. exact (eq_refl (term81 _127673 A v op u)). Qed.
Lemma lem6962421 {_127673 A : Type'} (v : A -> Prop) (u : A -> Prop) (op : type1400 _127673) (h1 : @monoidal _127673 op) : term76 _127673 A v op u.
Proof. exact (EQ_MP (@lem6962420 _127673 A v op u) (@lem6962419 _127673 A v u op h1)). Qed.
Lemma lem6962422 {_127673 A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> _127673) (op : type1400 _127673) (h1 : @monoidal _127673 op) : term82 _127673 A v op u f.
Proof. exact (@lem6962421 _127673 A v u op h1 f). Qed.
Lemma lem6962423 {_127673 A : Type'} (v : A -> Prop) (op : type1400 _127673) (u : A -> Prop) (f : A -> _127673) : (term82 _127673 A v op u f) = (term73 _127673 A v op u f).
Proof. exact (eq_refl (term82 _127673 A v op u f)). Qed.
Lemma lem6962426 {_127673 A : Type'} (v : A -> Prop) (u : A -> Prop) (f : A -> _127673) (op : type1400 _127673) (h1 : @monoidal _127673 op) : term73 _127673 A v op u f.
Proof. exact (EQ_MP (@lem6962423 _127673 A v op u f) (@lem6962422 _127673 A v u f op h1)). Qed.
Lemma lem6962427 {_127673 _127692 : Type'} (v : _127692 -> Prop) (u : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) (h1 : @monoidal _127673 op) : term73 _127673 _127692 v op u f.
Proof. exact (@lem6962426 _127673 _127692 v u f op h1). Qed.
Lemma lem6962428 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) (h1 : @monoidal _127673 op) : term83 _127673 _127692 op s f.
Proof. exact (@lem6962427 _127673 _127692 (@UNIV _127692) s f op h1). Qed.
Lemma lem6962456 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term10 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem6962457 {_127692 : Type'} (s : _127692 -> Prop) (t : _127692 -> Prop) : (@SUBSET _127692 s t) = (term10 _127692 s t).
Proof. exact (@lem6962456 _127692 s t). Qed.
Lemma lem6962458 {_127692 : Type'} (s : _127692 -> Prop) : (@SUBSET _127692 s (@UNIV _127692)) = (term84 _127692 s).
Proof. exact (@lem6962457 _127692 s (@UNIV _127692)). Qed.
Lemma lem6962465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6962466 {_127692 : Type'} (s : _127692 -> Prop) : (term85 _127692 s) = (term86 _127692 s).
Proof. exact (MK_COMB (@lem6962465) (@lem6962458 _127692 s)). Qed.
Lemma lem6962479 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term87 _127673 _127692 s f op) = (term87 _127673 _127692 s f op).
Proof. exact (eq_refl (term87 _127673 _127692 s f op)). Qed.
Lemma lem6962480 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term88 _127673 _127692 s f op) = (term89 _127673 _127692 s f op).
Proof. exact (MK_COMB (@lem6962466 _127692 s) (@lem6962479 _127673 _127692 s f op)). Qed.
Lemma lem6962483 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term48 _127673 _127692 f op s) = (term48 _127673 _127692 f op s).
Proof. exact (eq_refl (term48 _127673 _127692 f op s)). Qed.
Lemma lem6962484 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term90 _127673 _127692 s f op) = (term91 _127673 _127692 s f op).
Proof. exact (MK_COMB (@lem6962483 _127673 _127692 f op s) (@lem6962480 _127673 _127692 s f op)). Qed.
Lemma lem6962487 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term91 _127673 _127692 s f op) = (term90 _127673 _127692 s f op).
Proof. exact (SYM (@lem6962484 _127673 _127692 s f op)). Qed.
Lemma lem6962499 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem6962500 {_127692 : Type'} (x : _127692) : (@IN _127692 x (@UNIV _127692)) = True.
Proof. exact (@lem6962499 _127692 x). Qed.
Lemma lem6962501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6962502 {_127692 : Type'} (x : _127692) : (term92 _127692 x) = (and True).
Proof. exact (MK_COMB (@lem6962501) (@lem6962500 _127692 x)). Qed.
Lemma lem6962505 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term93 _127673 _127692 f x op) = (term93 _127673 _127692 f x op).
Proof. exact (eq_refl (term93 _127673 _127692 f x op)). Qed.
Lemma lem6962506 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term26 _127673 _127692 f x op) = (term94 _127673 _127692 f x op).
Proof. exact (MK_COMB (@lem6962502 _127692 x) (@lem6962505 _127673 _127692 f x op)). Qed.
Lemma lem6962508 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6962509 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term94 _127673 _127692 f x op) = (term93 _127673 _127692 f x op).
Proof. exact (@lem6962508 (term93 _127673 _127692 f x op)). Qed.
Lemma lem6962512 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term26 _127673 _127692 f x op) = (term93 _127673 _127692 f x op).
Proof. exact (TRANS (@lem6962506 _127673 _127692 f x op) (@lem6962509 _127673 _127692 f x op)). Qed.
Lemma lem6962513 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6962514 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term41 _127673 _127692 f x op) = (term95 _127673 _127692 f x op).
Proof. exact (MK_COMB (@lem6962513) (@lem6962512 _127673 _127692 f x op)). Qed.
Lemma lem6962516 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6962517 {_127692 : Type'} (P : _127692 -> Prop) (x : _127692) : (@IN _127692 x P) = (P x).
Proof. exact (@lem6962516 _127692 P x). Qed.
Lemma lem6962518 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) : (@IN _127692 x s) = (s x).
Proof. exact (@lem6962517 _127692 s x). Qed.
Lemma lem6962519 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (x : _127692) : (term43 _127673 _127692 f op x s) = (term96 _127673 _127692 f op s x).
Proof. exact (MK_COMB (@lem6962514 _127673 _127692 f x op) (@lem6962518 _127692 s x)). Qed.
Lemma lem6962522 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term45 _127673 _127692 f op s) = (term97 _127673 _127692 f op s).
Proof. exact (fun_ext (fun x : _127692 => @lem6962519 _127673 _127692 f op s x)). Qed.
Lemma lem6962523 {_127692 : Type'} : (@all _127692) = (@all _127692).
Proof. exact (eq_refl (@all _127692)). Qed.
Lemma lem6962524 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term46 _127673 _127692 f op s) = (term98 _127673 _127692 f op s).
Proof. exact (MK_COMB (@lem6962523 _127692) (@lem6962522 _127673 _127692 f op s)). Qed.
Lemma lem6962529 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6962530 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term48 _127673 _127692 f op s) = (term99 _127673 _127692 f op s).
Proof. exact (MK_COMB (@lem6962529) (@lem6962524 _127673 _127692 f op s)). Qed.
Lemma lem6962540 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6962541 {_127692 : Type'} (P : _127692 -> Prop) (x : _127692) : (@IN _127692 x P) = (P x).
Proof. exact (@lem6962540 _127692 P x). Qed.
Lemma lem6962542 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) : (@IN _127692 x s) = (s x).
Proof. exact (@lem6962541 _127692 s x). Qed.
Lemma lem6962543 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6962544 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) : (term100 _127692 x s) = (term101 _127692 s x).
Proof. exact (MK_COMB (@lem6962543) (@lem6962542 _127692 s x)). Qed.
Lemma lem6962546 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem6962547 {_127692 : Type'} (x : _127692) : (@IN _127692 x (@UNIV _127692)) = True.
Proof. exact (@lem6962546 _127692 x). Qed.
Lemma lem6962548 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) : (term102 _127692 s x) = (term103 _127692 s x).
Proof. exact (MK_COMB (@lem6962544 _127692 s x) (@lem6962547 _127692 x)). Qed.
Lemma lem6962550 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6962551 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) : (term103 _127692 s x) = True.
Proof. exact (@lem6962550 (s x)). Qed.
Lemma lem6962552 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) : (term102 _127692 s x) = True.
Proof. exact (TRANS (@lem6962548 _127692 s x) (@lem6962551 _127692 s x)). Qed.
Lemma lem6962553 {_127692 : Type'} (s : _127692 -> Prop) : (term104 _127692 s) = (term105 _127692).
Proof. exact (fun_ext (fun x : _127692 => @lem6962552 _127692 s x)). Qed.
Lemma lem6962554 {_127692 : Type'} : (@all _127692) = (@all _127692).
Proof. exact (eq_refl (@all _127692)). Qed.
Lemma lem6962555 {_127692 : Type'} (s : _127692 -> Prop) : (term84 _127692 s) = (term106 _127692).
Proof. exact (MK_COMB (@lem6962554 _127692) (@lem6962553 _127692 s)). Qed.
Lemma lem6962557 {A : Type'} (t : Prop) : (term107 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6962558 {_127692 : Type'} (t : Prop) : (term107 _127692 t) = t.
Proof. exact (@lem6962557 _127692 t). Qed.
Lemma lem6962559 {_127692 : Type'} : (term106 _127692) = True.
Proof. exact (@lem6962558 _127692 True). Qed.
Lemma lem6962560 {_127692 : Type'} (s : _127692 -> Prop) : (term84 _127692 s) = True.
Proof. exact (TRANS (@lem6962555 _127692 s) (@lem6962559 _127692)). Qed.
Lemma lem6962561 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6962562 {_127692 : Type'} (s : _127692 -> Prop) : (term86 _127692 s) = (and True).
Proof. exact (MK_COMB (@lem6962561) (@lem6962560 _127692 s)). Qed.
Lemma lem6962572 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem6962573 {_127692 : Type'} (x : _127692) : (@IN _127692 x (@UNIV _127692)) = True.
Proof. exact (@lem6962572 _127692 x). Qed.
Lemma lem6962574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6962575 {_127692 : Type'} (x : _127692) : (term92 _127692 x) = (and True).
Proof. exact (MK_COMB (@lem6962574) (@lem6962573 _127692 x)). Qed.
Lemma lem6962577 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6962578 {_127692 : Type'} (P : _127692 -> Prop) (x : _127692) : (@IN _127692 x P) = (P x).
Proof. exact (@lem6962577 _127692 P x). Qed.
Lemma lem6962579 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) : (@IN _127692 x s) = (s x).
Proof. exact (@lem6962578 _127692 s x). Qed.
Lemma lem6962580 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6962581 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) : (term108 _127692 x s) = (term109 _127692 s x).
Proof. exact (MK_COMB (@lem6962580) (@lem6962579 _127692 s x)). Qed.
Lemma lem6962582 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) : (term110 _127692 x s) = (term111 _127692 s x).
Proof. exact (MK_COMB (@lem6962575 _127692 x) (@lem6962581 _127692 s x)). Qed.
Lemma lem6962584 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6962585 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) : (term111 _127692 s x) = (term109 _127692 s x).
Proof. exact (@lem6962584 (term109 _127692 s x)). Qed.
Lemma lem6962586 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) : (term110 _127692 x s) = (term109 _127692 s x).
Proof. exact (TRANS (@lem6962582 _127692 s x) (@lem6962585 _127692 s x)). Qed.
Lemma lem6962587 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6962588 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) : (term112 _127692 x s) = (term113 _127692 s x).
Proof. exact (MK_COMB (@lem6962587) (@lem6962586 _127692 s x)). Qed.
Lemma lem6962591 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : ((f x) = (@neutral _127673 op)) = ((f x) = (@neutral _127673 op)).
Proof. exact (eq_refl ((f x) = (@neutral _127673 op))). Qed.
Lemma lem6962592 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term114 _127673 _127692 s f x op) = (term115 _127673 _127692 s f x op).
Proof. exact (MK_COMB (@lem6962588 _127692 s x) (@lem6962591 _127673 _127692 f x op)). Qed.
Lemma lem6962595 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term116 _127673 _127692 s f op) = (term117 _127673 _127692 s f op).
Proof. exact (fun_ext (fun x : _127692 => @lem6962592 _127673 _127692 s f x op)). Qed.
Lemma lem6962596 {_127692 : Type'} : (@all _127692) = (@all _127692).
Proof. exact (eq_refl (@all _127692)). Qed.
Lemma lem6962597 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term87 _127673 _127692 s f op) = (term118 _127673 _127692 s f op).
Proof. exact (MK_COMB (@lem6962596 _127692) (@lem6962595 _127673 _127692 s f op)). Qed.
Lemma lem6962602 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term89 _127673 _127692 s f op) = (term119 _127673 _127692 s f op).
Proof. exact (MK_COMB (@lem6962562 _127692 s) (@lem6962597 _127673 _127692 s f op)). Qed.
Lemma lem6962604 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6962605 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term119 _127673 _127692 s f op) = (term118 _127673 _127692 s f op).
Proof. exact (@lem6962604 (term118 _127673 _127692 s f op)). Qed.
Lemma lem6962614 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term89 _127673 _127692 s f op) = (term118 _127673 _127692 s f op).
Proof. exact (TRANS (@lem6962602 _127673 _127692 s f op) (@lem6962605 _127673 _127692 s f op)). Qed.
Lemma lem6962615 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term91 _127673 _127692 s f op) = (term120 _127673 _127692 s f op).
Proof. exact (MK_COMB (@lem6962530 _127673 _127692 f op s) (@lem6962614 _127673 _127692 s f op)). Qed.
Lemma lem6962618 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term120 _127673 _127692 s f op) = (term91 _127673 _127692 s f op).
Proof. exact (SYM (@lem6962615 _127673 _127692 s f op)). Qed.
Lemma lem6962620 (p : Prop) : p = (term121 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6962621 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term120 _127673 _127692 s f op) = (term122 _127673 _127692 s f op).
Proof. exact (@lem6962620 (term120 _127673 _127692 s f op)). Qed.
Lemma lem6962622 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term122 _127673 _127692 s f op) = (term120 _127673 _127692 s f op).
Proof. exact (SYM (@lem6962621 _127673 _127692 s f op)). Qed.
Lemma lem6962623 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) (h1 : term123 _127673 _127692 s f op) : term123 _127673 _127692 s f op.
Proof. exact (h1). Qed.
Lemma lem6962626 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) (h1 : term122 _127673 _127692 s f op) : term122 _127673 _127692 s f op.
Proof. exact (h1). Qed.
Lemma lem6962627 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : term124 _127673 _127692 s f op.
Proof. exact (fun h0 : term122 _127673 _127692 s f op => @lem6962626 _127673 _127692 s f op h0). Qed.
Lemma lem6962628 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) (h1 : term124 _127673 _127692 s f op) : term124 _127673 _127692 s f op.
Proof. exact (h1). Qed.
Lemma lem6962629 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) (h1 : term122 _127673 _127692 s f op) : term122 _127673 _127692 s f op.
Proof. exact (h1). Qed.
Lemma lem6962630 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) (h1 : term122 _127673 _127692 s f op) (h2 : term124 _127673 _127692 s f op) : term122 _127673 _127692 s f op.
Proof. exact (@lem6962628 _127673 _127692 s f op h2 (@lem6962629 _127673 _127692 s f op h1)). Qed.
Lemma lem6962631 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) (h1 : term122 _127673 _127692 s f op) : term125 _127673 _127692 s f op.
Proof. exact (fun h0 : term124 _127673 _127692 s f op => @lem6962630 _127673 _127692 s f op h1 h0). Qed.
Lemma lem6962632 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) (h1 : term124 _127673 _127692 s f op) : term124 _127673 _127692 s f op.
Proof. exact (h1). Qed.
Lemma lem6962633 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) (h1 : term122 _127673 _127692 s f op) (h2 : term124 _127673 _127692 s f op) : term122 _127673 _127692 s f op.
Proof. exact (@lem6962631 _127673 _127692 s f op h1 (@lem6962632 _127673 _127692 s f op h2)). Qed.
Lemma lem6962634 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) (h1 : term124 _127673 _127692 s f op) : term124 _127673 _127692 s f op.
Proof. exact (fun h0 : term122 _127673 _127692 s f op => @lem6962633 _127673 _127692 s f op h0 h1). Qed.
Lemma lem6962635 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : term126 _127673 _127692 s f op.
Proof. exact (fun h0 : term124 _127673 _127692 s f op => @lem6962634 _127673 _127692 s f op h0). Qed.
Lemma lem6962638 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : term124 _127673 _127692 s f op.
Proof. exact (@lem6962635 _127673 _127692 s f op (@lem6962627 _127673 _127692 s f op)). Qed.
Lemma lem6962639 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : term124 _127673 _127692 s f op.
Proof. exact (@lem6962638 _127673 _127692 s f op). Qed.
Lemma lem6962653 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6962654 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term122 _127673 _127692 s f op) = (term127 _127673 _127692 s f op).
Proof. exact (@lem6962653 (term123 _127673 _127692 s f op)). Qed.
Lemma lem6962656 (t : Prop) : (term128 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6962657 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term127 _127673 _127692 s f op) = (term120 _127673 _127692 s f op).
Proof. exact (@lem6962656 (term120 _127673 _127692 s f op)). Qed.
Lemma lem6962660 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term122 _127673 _127692 s f op) = (term120 _127673 _127692 s f op).
Proof. exact (TRANS (@lem6962654 _127673 _127692 s f op) (@lem6962657 _127673 _127692 s f op)). Qed.
Lemma lem6962673 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) : (term129 _127673 _127692 f op) = (term130 _127673 _127692 f op).
Proof. exact (fun_ext (fun s : _127692 -> Prop => @lem6962660 _127673 _127692 s f op)). Qed.
Lemma lem6962674 {_127692 : Type'} : (@all (_127692 -> Prop)) = (@all (_127692 -> Prop)).
Proof. exact (eq_refl (@all (_127692 -> Prop))). Qed.
Lemma lem6962675 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) : (term131 _127673 _127692 f op) = (term132 _127673 _127692 f op).
Proof. exact (MK_COMB (@lem6962674 _127692) (@lem6962673 _127673 _127692 f op)). Qed.
Lemma lem6962680 {_127673 _127692 : Type'} (op : type1400 _127673) : (term133 _127673 _127692 op) = (term134 _127673 _127692 op).
Proof. exact (fun_ext (fun f : _127692 -> _127673 => @lem6962675 _127673 _127692 f op)). Qed.
Lemma lem6962681 {_127673 _127692 : Type'} : (@all (_127692 -> _127673)) = (@all (_127692 -> _127673)).
Proof. exact (eq_refl (@all (_127692 -> _127673))). Qed.
Lemma lem6962682 {_127673 _127692 : Type'} (op : type1400 _127673) : (term135 _127673 _127692 op) = (term136 _127673 _127692 op).
Proof. exact (MK_COMB (@lem6962681 _127673 _127692) (@lem6962680 _127673 _127692 op)). Qed.
Lemma lem6962687 {_127673 _127692 : Type'} : (term137 _127673 _127692) = (term138 _127673 _127692).
Proof. exact (fun_ext (fun op : type1400 _127673 => @lem6962682 _127673 _127692 op)). Qed.
Lemma lem6962688 {_127673 : Type'} : (@all (_127673 -> _127673 -> _127673)) = (@all (_127673 -> _127673 -> _127673)).
Proof. exact (eq_refl (@all (_127673 -> _127673 -> _127673))). Qed.
Lemma lem6962697 {_127673 _127692 : Type'} : (term139 _127673 _127692) = (term140 _127673 _127692).
Proof. exact (MK_COMB (@lem6962688 _127673) (@lem6962687 _127673 _127692)). Qed.
Lemma lem6962704 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term115 _127673 _127692 s f x op) = (term115 _127673 _127692 s f x op).
Proof. exact (eq_refl (term115 _127673 _127692 s f x op)). Qed.
Lemma lem6962705 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term117 _127673 _127692 s f op) = (term117 _127673 _127692 s f op).
Proof. exact (fun_ext (fun x : _127692 => @lem6962704 _127673 _127692 s f x op)). Qed.
Lemma lem6962706 {_127692 : Type'} : (@all _127692) = (@all _127692).
Proof. exact (eq_refl (@all _127692)). Qed.
Lemma lem6962707 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term118 _127673 _127692 s f op) = (term118 _127673 _127692 s f op).
Proof. exact (MK_COMB (@lem6962706 _127692) (@lem6962705 _127673 _127692 s f op)). Qed.
Lemma lem6962714 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (x : _127692) : (term96 _127673 _127692 f op s x) = (term96 _127673 _127692 f op s x).
Proof. exact (eq_refl (term96 _127673 _127692 f op s x)). Qed.
Lemma lem6962715 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term97 _127673 _127692 f op s) = (term97 _127673 _127692 f op s).
Proof. exact (fun_ext (fun x : _127692 => @lem6962714 _127673 _127692 f op s x)). Qed.
Lemma lem6962716 {_127692 : Type'} : (@all _127692) = (@all _127692).
Proof. exact (eq_refl (@all _127692)). Qed.
Lemma lem6962717 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term98 _127673 _127692 f op s) = (term98 _127673 _127692 f op s).
Proof. exact (MK_COMB (@lem6962716 _127692) (@lem6962715 _127673 _127692 f op s)). Qed.
Lemma lem6962718 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6962719 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term99 _127673 _127692 f op s) = (term99 _127673 _127692 f op s).
Proof. exact (MK_COMB (@lem6962718) (@lem6962717 _127673 _127692 f op s)). Qed.
Lemma lem6962720 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term120 _127673 _127692 s f op) = (term120 _127673 _127692 s f op).
Proof. exact (MK_COMB (@lem6962719 _127673 _127692 f op s) (@lem6962707 _127673 _127692 s f op)). Qed.
Lemma lem6962721 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) : (term130 _127673 _127692 f op) = (term130 _127673 _127692 f op).
Proof. exact (fun_ext (fun s : _127692 -> Prop => @lem6962720 _127673 _127692 s f op)). Qed.
Lemma lem6962722 {_127692 : Type'} : (@all (_127692 -> Prop)) = (@all (_127692 -> Prop)).
Proof. exact (eq_refl (@all (_127692 -> Prop))). Qed.
Lemma lem6962723 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) : (term132 _127673 _127692 f op) = (term132 _127673 _127692 f op).
Proof. exact (MK_COMB (@lem6962722 _127692) (@lem6962721 _127673 _127692 f op)). Qed.
Lemma lem6962724 {_127673 _127692 : Type'} (op : type1400 _127673) : (term134 _127673 _127692 op) = (term134 _127673 _127692 op).
Proof. exact (fun_ext (fun f : _127692 -> _127673 => @lem6962723 _127673 _127692 f op)). Qed.
Lemma lem6962725 {_127673 _127692 : Type'} : (@all (_127692 -> _127673)) = (@all (_127692 -> _127673)).
Proof. exact (eq_refl (@all (_127692 -> _127673))). Qed.
Lemma lem6962726 {_127673 _127692 : Type'} (op : type1400 _127673) : (term136 _127673 _127692 op) = (term136 _127673 _127692 op).
Proof. exact (MK_COMB (@lem6962725 _127673 _127692) (@lem6962724 _127673 _127692 op)). Qed.
Lemma lem6962727 {_127673 _127692 : Type'} : (term138 _127673 _127692) = (term138 _127673 _127692).
Proof. exact (fun_ext (fun op : type1400 _127673 => @lem6962726 _127673 _127692 op)). Qed.
Lemma lem6962728 {_127673 : Type'} : (@all (_127673 -> _127673 -> _127673)) = (@all (_127673 -> _127673 -> _127673)).
Proof. exact (eq_refl (@all (_127673 -> _127673 -> _127673))). Qed.
Lemma lem6962729 {_127673 _127692 : Type'} : (term140 _127673 _127692) = (term140 _127673 _127692).
Proof. exact (MK_COMB (@lem6962728 _127673) (@lem6962727 _127673 _127692)). Qed.
Lemma lem6962768 {_127673 _127692 : Type'} : (term139 _127673 _127692) = (term140 _127673 _127692).
Proof. exact (TRANS (@lem6962697 _127673 _127692) (@lem6962729 _127673 _127692)). Qed.
Lemma lem6962769 {_127673 _127692 : Type'} : (term140 _127673 _127692) = (term139 _127673 _127692).
Proof. exact (SYM (@lem6962768 _127673 _127692)). Qed.
Lemma lem6962770 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (h1 : term98 _127673 _127692 f op s) : term98 _127673 _127692 f op s.
Proof. exact (h1). Qed.
Lemma lem6962773 (p : Prop) : p = (term121 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6962774 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : ((f x) = (@neutral _127673 op)) = (term141 _127673 _127692 f x op).
Proof. exact (@lem6962773 ((f x) = (@neutral _127673 op))). Qed.
Lemma lem6962775 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term141 _127673 _127692 f x op) = ((f x) = (@neutral _127673 op)).
Proof. exact (SYM (@lem6962774 _127673 _127692 f x op)). Qed.
Lemma lem6962776 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term93 _127673 _127692 f x op) : term93 _127673 _127692 f x op.
Proof. exact (h1). Qed.
Lemma lem6962779 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term142 _127673 _127692 f x op) = ((f x) = (@neutral _127673 op)).
Proof. exact (@lem16933 ((f x) = (@neutral _127673 op))). Qed.
Lemma lem6962780 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem6962781 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6962782 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term143 _127673 _127692 f x op) = (term144 _127673 _127692 f x op).
Proof. exact (MK_COMB (@lem6962781) (@lem6962779 _127673 _127692 f x op)). Qed.
Lemma lem6962783 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (x : _127692) : (term145 _127673 _127692 f op s x) = (term146 _127673 _127692 f op s x).
Proof. exact (MK_COMB (@lem6962782 _127673 _127692 f x op) (@lem6962780 _127692 s x)). Qed.
Lemma lem6962784 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (x : _127692) : (term96 _127673 _127692 f op s x) = (term145 _127673 _127692 f op s x).
Proof. exact (@lem17265 (term93 _127673 _127692 f x op) (s x)). Qed.
Lemma lem6962785 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (x : _127692) : (term96 _127673 _127692 f op s x) = (term146 _127673 _127692 f op s x).
Proof. exact (TRANS (@lem6962784 _127673 _127692 f op s x) (@lem6962783 _127673 _127692 f op s x)). Qed.
Lemma lem6962786 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term97 _127673 _127692 f op s) = (term147 _127673 _127692 f op s).
Proof. exact (fun_ext (fun x : _127692 => @lem6962785 _127673 _127692 f op s x)). Qed.
Lemma lem6962787 {_127692 : Type'} : (@all _127692) = (@all _127692).
Proof. exact (eq_refl (@all _127692)). Qed.
Lemma lem6962824 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term98 _127673 _127692 f op s) = (term148 _127673 _127692 f op s).
Proof. exact (MK_COMB (@lem6962787 _127692) (@lem6962786 _127673 _127692 f op s)). Qed.
Lemma lem6962825 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (h1 : term98 _127673 _127692 f op s) : term148 _127673 _127692 f op s.
Proof. exact (EQ_MP (@lem6962824 _127673 _127692 f op s) (@lem6962770 _127673 _127692 f op s h1)). Qed.
Lemma lem6962831 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) (h1 : term109 _127692 s x) : term109 _127692 s x.
Proof. exact (h1). Qed.
Lemma lem6962837 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term93 _127673 _127692 f x op) : term93 _127673 _127692 f x op.
Proof. exact (h1). Qed.
Lemma lem6962852 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (x : _127692) : (term146 _127673 _127692 f op s x) = (term146 _127673 _127692 f op s x).
Proof. exact (eq_refl (term146 _127673 _127692 f op s x)). Qed.
Lemma lem6962853 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term147 _127673 _127692 f op s) = (term147 _127673 _127692 f op s).
Proof. exact (fun_ext (fun x : _127692 => @lem6962852 _127673 _127692 f op s x)). Qed.
Lemma lem6962854 {_127692 : Type'} : (@all _127692) = (@all _127692).
Proof. exact (eq_refl (@all _127692)). Qed.
Lemma lem6962855 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term148 _127673 _127692 f op s) = (term148 _127673 _127692 f op s).
Proof. exact (MK_COMB (@lem6962854 _127692) (@lem6962853 _127673 _127692 f op s)). Qed.
Lemma lem6962856 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (h1 : term98 _127673 _127692 f op s) : term148 _127673 _127692 f op s.
Proof. exact (EQ_MP (@lem6962855 _127673 _127692 f op s) (@lem6962825 _127673 _127692 f op s h1)). Qed.
Lemma lem6962862 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) (h1 : term109 _127692 s x) : term109 _127692 s x.
Proof. exact (h1). Qed.
Lemma lem6962874 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term93 _127673 _127692 f x op) : term93 _127673 _127692 f x op.
Proof. exact (h1). Qed.
Lemma lem6962882 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (x : _127692) : (term146 _127673 _127692 f op s x) = (term146 _127673 _127692 f op s x).
Proof. exact (eq_refl (term146 _127673 _127692 f op s x)). Qed.
Lemma lem6962883 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term147 _127673 _127692 f op s) = (term147 _127673 _127692 f op s).
Proof. exact (fun_ext (fun x : _127692 => @lem6962882 _127673 _127692 f op s x)). Qed.
Lemma lem6962884 {_127692 : Type'} : (@all _127692) = (@all _127692).
Proof. exact (eq_refl (@all _127692)). Qed.
Lemma lem6962886 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : (term148 _127673 _127692 f op s) = (term148 _127673 _127692 f op s).
Proof. exact (MK_COMB (@lem6962884 _127692) (@lem6962883 _127673 _127692 f op s)). Qed.
Lemma lem6962887 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (h1 : term98 _127673 _127692 f op s) : term148 _127673 _127692 f op s.
Proof. exact (EQ_MP (@lem6962886 _127673 _127692 f op s) (@lem6962856 _127673 _127692 f op s h1)). Qed.
Lemma lem6962891 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) (h1 : term109 _127692 s x) : term109 _127692 s x.
Proof. exact (h1). Qed.
Lemma lem6962895 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term93 _127673 _127692 f x op) : term93 _127673 _127692 f x op.
Proof. exact (h1). Qed.
Lemma lem6962896 {_127673 _127692 : Type'} (_92729 : _127692) (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (h1 : term98 _127673 _127692 f op s) : term149 _127673 _127692 f op s _92729.
Proof. exact (@lem6962887 _127673 _127692 f op s h1 _92729). Qed.
Lemma lem6962897 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (_92729 : _127692) : (term149 _127673 _127692 f op s _92729) = (term146 _127673 _127692 f op s _92729).
Proof. exact (eq_refl (term149 _127673 _127692 f op s _92729)). Qed.
Lemma lem6962904 {_127673 _127692 : Type'} (_92729 : _127692) (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (h1 : term98 _127673 _127692 f op s) : term146 _127673 _127692 f op s _92729.
Proof. exact (EQ_MP (@lem6962897 _127673 _127692 f op s _92729) (@lem6962896 _127673 _127692 _92729 f op s h1)). Qed.
Lemma lem6962906 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) (h1 : term109 _127692 s x) : term109 _127692 s x.
Proof. exact (h1). Qed.
Lemma lem6962908 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term93 _127673 _127692 f x op) : term93 _127673 _127692 f x op.
Proof. exact (h1). Qed.
Lemma lem6962944 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) (h1 : term109 _127692 s x) : term109 _127692 s x.
Proof. exact (h1). Qed.
Lemma lem6962945 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) (h1 : term109 _127692 s x) : term150 _127692 s x.
Proof. exact (fun h0 : s x => @lem6962944 _127692 s x h1). Qed.
Lemma lem6962947 (p : Prop) : (term151 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6962948 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) : (term150 _127692 s x) = (term109 _127692 s x).
Proof. exact (@lem6962947 (s x)). Qed.
Lemma lem6962949 {_127692 : Type'} (s : _127692 -> Prop) (x : _127692) (h1 : term109 _127692 s x) : term109 _127692 s x.
Proof. exact (EQ_MP (@lem6962948 _127692 s x) (@lem6962945 _127692 s x h1)). Qed.
Lemma lem6962951 (b : Prop) (a : Prop) : (a \/ b) = (term152 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6962954 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (_92729 : _127692) (op : type1400 _127673) : (term146 _127673 _127692 f op s _92729) = (term115 _127673 _127692 s f _92729 op).
Proof. exact (@lem6962951 (s _92729) ((f _92729) = (@neutral _127673 op))). Qed.
Lemma lem6962957 {_127673 _127692 : Type'} (_92729 : _127692) (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (h1 : term98 _127673 _127692 f op s) : term115 _127673 _127692 s f _92729 op.
Proof. exact (EQ_MP (@lem6962954 _127673 _127692 s f _92729 op) (@lem6962904 _127673 _127692 _92729 f op s h1)). Qed.
Lemma lem6962958 {_127673 _127692 : Type'} (_92729 : _127692) (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (h1 : term98 _127673 _127692 f op s) : term115 _127673 _127692 s f _92729 op.
Proof. exact (@lem6962957 _127673 _127692 _92729 f op s h1). Qed.
Lemma lem6962959 {_127673 _127692 : Type'} (x : _127692) (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (h1 : term98 _127673 _127692 f op s) : term115 _127673 _127692 s f x op.
Proof. exact (@lem6962958 _127673 _127692 x f op s h1). Qed.
Lemma lem6962962 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (x : _127692) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) : (f x) = (@neutral _127673 op).
Proof. exact (@lem6962959 _127673 _127692 x f op s h1 (@lem6962949 _127692 s x h2)). Qed.
Lemma lem6962963 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (x : _127692) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) : term153 _127673 _127692 f x op.
Proof. exact (fun h0 : term93 _127673 _127692 f x op => @lem6962962 _127673 _127692 f op s x h1 h2). Qed.
Lemma lem6962965 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6962966 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term153 _127673 _127692 f x op) = ((f x) = (@neutral _127673 op)).
Proof. exact (@lem6962965 ((f x) = (@neutral _127673 op))). Qed.
Lemma lem6962967 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (x : _127692) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) : (f x) = (@neutral _127673 op).
Proof. exact (EQ_MP (@lem6962966 _127673 _127692 f x op) (@lem6962963 _127673 _127692 f op s x h1 h2)). Qed.
Lemma lem6962970 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6962972 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) : (term93 _127673 _127692 f x op) = (term155 _127673 _127692 f x op).
Proof. exact (@lem6962970 ((f x) = (@neutral _127673 op))). Qed.
Lemma lem6962975 {_127673 _127692 : Type'} (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term93 _127673 _127692 f x op) : term155 _127673 _127692 f x op.
Proof. exact (EQ_MP (@lem6962972 _127673 _127692 f x op) (@lem6962908 _127673 _127692 f x op h1)). Qed.
Lemma lem6962978 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : False.
Proof. exact (@lem6962975 _127673 _127692 f x op h3 (@lem6962967 _127673 _127692 f op s x h1 h2)). Qed.
Lemma lem6962979 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : term156.
Proof. exact (fun h0 : ~ False => @lem6962978 _127673 _127692 s f x op h1 h2 h3). Qed.
Lemma lem6962981 (p : Prop) : (term154 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6962982 : term156 = False.
Proof. exact (@lem6962981 False). Qed.
Lemma lem6962983 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : False.
Proof. exact (EQ_MP (@lem6962982) (@lem6962979 _127673 _127692 s f x op h1 h2 h3)). Qed.
Lemma lem6962984 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : (term93 _127673 _127692 f x op) = False.
Proof. exact (prop_ext (fun h4 : term93 _127673 _127692 f x op => @lem6962983 _127673 _127692 s f x op h1 h2 h3) (fun h4 : False => @lem6962908 _127673 _127692 f x op h3)). Qed.
Lemma lem6962985 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : False.
Proof. exact (EQ_MP (@lem6962984 _127673 _127692 s f x op h1 h2 h3) (@lem6962908 _127673 _127692 f x op h3)). Qed.
Lemma lem6962986 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : (term109 _127692 s x) = False.
Proof. exact (prop_ext (fun h4 : term109 _127692 s x => @lem6962985 _127673 _127692 s f x op h1 h2 h3) (fun h4 : False => @lem6962906 _127692 s x h2)). Qed.
Lemma lem6962987 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : False.
Proof. exact (EQ_MP (@lem6962986 _127673 _127692 s f x op h1 h2 h3) (@lem6962906 _127692 s x h2)). Qed.
Lemma lem6962988 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : (term93 _127673 _127692 f x op) = False.
Proof. exact (prop_ext (fun h4 : term93 _127673 _127692 f x op => @lem6962987 _127673 _127692 s f x op h1 h2 h3) (fun h4 : False => @lem6962895 _127673 _127692 f x op h3)). Qed.
Lemma lem6962989 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : False.
Proof. exact (EQ_MP (@lem6962988 _127673 _127692 s f x op h1 h2 h3) (@lem6962895 _127673 _127692 f x op h3)). Qed.
Lemma lem6962990 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : (term109 _127692 s x) = False.
Proof. exact (prop_ext (fun h4 : term109 _127692 s x => @lem6962989 _127673 _127692 s f x op h1 h2 h3) (fun h4 : False => @lem6962891 _127692 s x h2)). Qed.
Lemma lem6962991 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : False.
Proof. exact (EQ_MP (@lem6962990 _127673 _127692 s f x op h1 h2 h3) (@lem6962891 _127692 s x h2)). Qed.
Lemma lem6962992 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : (term93 _127673 _127692 f x op) = False.
Proof. exact (prop_ext (fun h4 : term93 _127673 _127692 f x op => @lem6962991 _127673 _127692 s f x op h1 h2 h3) (fun h4 : False => @lem6962895 _127673 _127692 f x op h3)). Qed.
Lemma lem6962993 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : False.
Proof. exact (EQ_MP (@lem6962992 _127673 _127692 s f x op h1 h2 h3) (@lem6962895 _127673 _127692 f x op h3)). Qed.
Lemma lem6962994 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : (term109 _127692 s x) = False.
Proof. exact (prop_ext (fun h4 : term109 _127692 s x => @lem6962993 _127673 _127692 s f x op h1 h2 h3) (fun h4 : False => @lem6962891 _127692 s x h2)). Qed.
Lemma lem6962995 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : False.
Proof. exact (EQ_MP (@lem6962994 _127673 _127692 s f x op h1 h2 h3) (@lem6962891 _127692 s x h2)). Qed.
Lemma lem6962996 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : (term93 _127673 _127692 f x op) = False.
Proof. exact (prop_ext (fun h4 : term93 _127673 _127692 f x op => @lem6962995 _127673 _127692 s f x op h1 h2 h3) (fun h4 : False => @lem6962874 _127673 _127692 f x op h3)). Qed.
Lemma lem6962997 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : False.
Proof. exact (EQ_MP (@lem6962996 _127673 _127692 s f x op h1 h2 h3) (@lem6962874 _127673 _127692 f x op h3)). Qed.
Lemma lem6962998 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : (term109 _127692 s x) = False.
Proof. exact (prop_ext (fun h4 : term109 _127692 s x => @lem6962997 _127673 _127692 s f x op h1 h2 h3) (fun h4 : False => @lem6962862 _127692 s x h2)). Qed.
Lemma lem6962999 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : False.
Proof. exact (EQ_MP (@lem6962998 _127673 _127692 s f x op h1 h2 h3) (@lem6962862 _127692 s x h2)). Qed.
Lemma lem6963000 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : (term93 _127673 _127692 f x op) = False.
Proof. exact (prop_ext (fun h4 : term93 _127673 _127692 f x op => @lem6962999 _127673 _127692 s f x op h1 h2 h3) (fun h4 : False => @lem6962837 _127673 _127692 f x op h3)). Qed.
Lemma lem6963001 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : False.
Proof. exact (EQ_MP (@lem6963000 _127673 _127692 s f x op h1 h2 h3) (@lem6962837 _127673 _127692 f x op h3)). Qed.
Lemma lem6963002 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : (term109 _127692 s x) = False.
Proof. exact (prop_ext (fun h4 : term109 _127692 s x => @lem6963001 _127673 _127692 s f x op h1 h2 h3) (fun h4 : False => @lem6962831 _127692 s x h2)). Qed.
Lemma lem6963003 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : False.
Proof. exact (EQ_MP (@lem6963002 _127673 _127692 s f x op h1 h2 h3) (@lem6962831 _127692 s x h2)). Qed.
Lemma lem6963004 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : (term93 _127673 _127692 f x op) = False.
Proof. exact (prop_ext (fun h4 : term93 _127673 _127692 f x op => @lem6963003 _127673 _127692 s f x op h1 h2 h3) (fun h4 : False => @lem6962776 _127673 _127692 f x op h3)). Qed.
Lemma lem6963005 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (x : _127692) (op : type1400 _127673) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) (h3 : term93 _127673 _127692 f x op) : False.
Proof. exact (EQ_MP (@lem6963004 _127673 _127692 s f x op h1 h2 h3) (@lem6962776 _127673 _127692 f x op h3)). Qed.
Lemma lem6963006 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (x : _127692) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) : term141 _127673 _127692 f x op.
Proof. exact (fun h0 : term93 _127673 _127692 f x op => @lem6963005 _127673 _127692 s f x op h1 h2 h0). Qed.
Lemma lem6963007 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (x : _127692) (h1 : term98 _127673 _127692 f op s) (h2 : term109 _127692 s x) : (f x) = (@neutral _127673 op).
Proof. exact (EQ_MP (@lem6962775 _127673 _127692 f x op) (@lem6963006 _127673 _127692 f op s x h1 h2)). Qed.
Lemma lem6963008 {_127673 _127692 : Type'} (x : _127692) (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (h1 : term98 _127673 _127692 f op s) : term115 _127673 _127692 s f x op.
Proof. exact (fun h0 : term109 _127692 s x => @lem6963007 _127673 _127692 f op s x h1 h0). Qed.
Lemma lem6963013 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (h1 : term98 _127673 _127692 f op s) : term118 _127673 _127692 s f op.
Proof. exact (fun x : _127692 => @lem6963008 _127673 _127692 x f op s h1). Qed.
Lemma lem6963014 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : term120 _127673 _127692 s f op.
Proof. exact (fun h0 : term98 _127673 _127692 f op s => @lem6963013 _127673 _127692 f op s h0). Qed.
Lemma lem6963019 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) : term132 _127673 _127692 f op.
Proof. exact (fun s : _127692 -> Prop => @lem6963014 _127673 _127692 s f op). Qed.
Lemma lem6963024 {_127673 _127692 : Type'} (op : type1400 _127673) : term136 _127673 _127692 op.
Proof. exact (fun f : _127692 -> _127673 => @lem6963019 _127673 _127692 f op). Qed.
Lemma lem6963029 {_127673 _127692 : Type'} : term140 _127673 _127692.
Proof. exact (fun op : type1400 _127673 => @lem6963024 _127673 _127692 op). Qed.
Lemma lem6963030 {_127673 _127692 : Type'} : term139 _127673 _127692.
Proof. exact (EQ_MP (@lem6962769 _127673 _127692) (@lem6963029 _127673 _127692)). Qed.
Lemma lem6963031 {_127673 _127692 : Type'} (op : type1400 _127673) : term157 _127673 _127692 op.
Proof. exact (@lem6963030 _127673 _127692 op). Qed.
Lemma lem6963032 {_127673 _127692 : Type'} (op : type1400 _127673) : (term157 _127673 _127692 op) = (term135 _127673 _127692 op).
Proof. exact (eq_refl (term157 _127673 _127692 op)). Qed.
Lemma lem6963033 {_127673 _127692 : Type'} (op : type1400 _127673) : term135 _127673 _127692 op.
Proof. exact (EQ_MP (@lem6963032 _127673 _127692 op) (@lem6963031 _127673 _127692 op)). Qed.
Lemma lem6963034 {_127673 _127692 : Type'} (op : type1400 _127673) (f : _127692 -> _127673) : term158 _127673 _127692 op f.
Proof. exact (@lem6963033 _127673 _127692 op f). Qed.
Lemma lem6963035 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) : (term158 _127673 _127692 op f) = (term131 _127673 _127692 f op).
Proof. exact (eq_refl (term158 _127673 _127692 op f)). Qed.
Lemma lem6963036 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) : term131 _127673 _127692 f op.
Proof. exact (EQ_MP (@lem6963035 _127673 _127692 f op) (@lem6963034 _127673 _127692 op f)). Qed.
Lemma lem6963037 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) : term159 _127673 _127692 f op s.
Proof. exact (@lem6963036 _127673 _127692 f op s). Qed.
Lemma lem6963038 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : (term159 _127673 _127692 f op s) = (term122 _127673 _127692 s f op).
Proof. exact (eq_refl (term159 _127673 _127692 f op s)). Qed.
Lemma lem6963039 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : term122 _127673 _127692 s f op.
Proof. exact (EQ_MP (@lem6963038 _127673 _127692 s f op) (@lem6963037 _127673 _127692 f op s)). Qed.
Lemma lem6963041 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : term122 _127673 _127692 s f op.
Proof. exact (@lem6962639 _127673 _127692 s f op (@lem6963039 _127673 _127692 s f op)). Qed.
Lemma lem6963042 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) (h1 : term123 _127673 _127692 s f op) : False.
Proof. exact (@lem6963041 _127673 _127692 s f op (@lem6962623 _127673 _127692 s f op h1)). Qed.
Lemma lem6963043 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) (h1 : term123 _127673 _127692 s f op) : (term123 _127673 _127692 s f op) = False.
Proof. exact (prop_ext (fun h2 : term123 _127673 _127692 s f op => @lem6963042 _127673 _127692 s f op h1) (fun h2 : False => @lem6962623 _127673 _127692 s f op h1)). Qed.
Lemma lem6963044 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) (h1 : term123 _127673 _127692 s f op) : False.
Proof. exact (EQ_MP (@lem6963043 _127673 _127692 s f op h1) (@lem6962623 _127673 _127692 s f op h1)). Qed.
Lemma lem6963045 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : term122 _127673 _127692 s f op.
Proof. exact (fun h0 : term123 _127673 _127692 s f op => @lem6963044 _127673 _127692 s f op h0). Qed.
Lemma lem6963046 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : term120 _127673 _127692 s f op.
Proof. exact (EQ_MP (@lem6962622 _127673 _127692 s f op) (@lem6963045 _127673 _127692 s f op)). Qed.
Lemma lem6963047 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : term91 _127673 _127692 s f op.
Proof. exact (EQ_MP (@lem6962618 _127673 _127692 s f op) (@lem6963046 _127673 _127692 s f op)). Qed.
Lemma lem6963048 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) : term90 _127673 _127692 s f op.
Proof. exact (EQ_MP (@lem6962487 _127673 _127692 s f op) (@lem6963047 _127673 _127692 s f op)). Qed.
Lemma lem6963049 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (s : _127692 -> Prop) (h1 : term46 _127673 _127692 f op s) : term88 _127673 _127692 s f op.
Proof. exact (@lem6963048 _127673 _127692 s f op (@lem6962382 _127673 _127692 f op s h1)). Qed.
Lemma lem6963050 {_127673 _127692 : Type'} (f : _127692 -> _127673) (s : _127692 -> Prop) (op : type1400 _127673) (h1 : term46 _127673 _127692 f op s) (h2 : @monoidal _127673 op) : (@iterate _127673 _127692 op (@UNIV _127692) f) = (@iterate _127673 _127692 op s f).
Proof. exact (@lem6962428 _127673 _127692 s f op h2 (@lem6963049 _127673 _127692 f op s h1)). Qed.
Lemma lem6963051 {_127673 _127692 : Type'} (f : _127692 -> _127673) (s : _127692 -> Prop) (op : type1400 _127673) (h1 : term46 _127673 _127692 f op s) (h2 : @monoidal _127673 op) : (@iterate _127673 _127692 op s f) = (@iterate _127673 _127692 op (@UNIV _127692) f).
Proof. exact (EQ_MP (@lem6962388 _127673 _127692 s op f) (@lem6963050 _127673 _127692 f s op h1 h2)). Qed.
Lemma lem6963052 {_127673 _127692 : Type'} (f : _127692 -> _127673) (s : _127692 -> Prop) (op : type1400 _127673) (h1 : term46 _127673 _127692 f op s) (h2 : @monoidal _127673 op) : (term46 _127673 _127692 f op s) = ((@iterate _127673 _127692 op s f) = (@iterate _127673 _127692 op (@UNIV _127692) f)).
Proof. exact (prop_ext (fun h3 : term46 _127673 _127692 f op s => @lem6963051 _127673 _127692 f s op h1 h2) (fun h3 : (@iterate _127673 _127692 op s f) = (@iterate _127673 _127692 op (@UNIV _127692) f) => @lem6962382 _127673 _127692 f op s h1)). Qed.
Lemma lem6963053 {_127673 _127692 : Type'} (f : _127692 -> _127673) (s : _127692 -> Prop) (op : type1400 _127673) (h1 : term46 _127673 _127692 f op s) (h2 : @monoidal _127673 op) : (@iterate _127673 _127692 op s f) = (@iterate _127673 _127692 op (@UNIV _127692) f).
Proof. exact (EQ_MP (@lem6963052 _127673 _127692 f s op h1 h2) (@lem6962382 _127673 _127692 f op s h1)). Qed.
Lemma lem6963054 {_127673 _127692 : Type'} (s : _127692 -> Prop) (f : _127692 -> _127673) (op : type1400 _127673) (h1 : @monoidal _127673 op) : term50 _127673 _127692 s op f.
Proof. exact (fun h0 : term46 _127673 _127692 f op s => @lem6963053 _127673 _127692 f s op h0 h1). Qed.
Lemma lem6963059 {_127673 _127692 : Type'} (f : _127692 -> _127673) (op : type1400 _127673) (h1 : @monoidal _127673 op) : term54 _127673 _127692 op f.
Proof. exact (fun s : _127692 -> Prop => @lem6963054 _127673 _127692 s f op h1). Qed.
Lemma lem6963064 {_127673 _127692 : Type'} (op : type1400 _127673) (h1 : @monoidal _127673 op) : term58 _127673 _127692 op.
Proof. exact (fun f : _127692 -> _127673 => @lem6963059 _127673 _127692 f op h1). Qed.
Lemma lem6963065 {_127673 _127692 : Type'} (op : type1400 _127673) (h1 : @monoidal _127673 op) : (@monoidal _127673 op) = (term58 _127673 _127692 op).
Proof. exact (prop_ext (fun h2 : @monoidal _127673 op => @lem6963064 _127673 _127692 op h1) (fun h2 : term58 _127673 _127692 op => @lem6962381 _127673 op h1)). Qed.
Lemma lem6963066 {_127673 _127692 : Type'} (op : type1400 _127673) (h1 : @monoidal _127673 op) : term58 _127673 _127692 op.
Proof. exact (EQ_MP (@lem6963065 _127673 _127692 op h1) (@lem6962381 _127673 op h1)). Qed.
Lemma lem6963067 {_127673 _127692 : Type'} (op : type1400 _127673) : term61 _127673 _127692 op.
Proof. exact (fun h0 : @monoidal _127673 op => @lem6963066 _127673 _127692 op h0). Qed.
Lemma lem6963072 {_127673 _127692 : Type'} : term65 _127673 _127692.
Proof. exact (fun op : type1400 _127673 => @lem6963067 _127673 _127692 op). Qed.
Lemma lem6963073 {_127673 _127692 : Type'} : term64 _127673 _127692.
Proof. exact (EQ_MP (@lem6962380 _127673 _127692) (@lem6963072 _127673 _127692)). Qed.
