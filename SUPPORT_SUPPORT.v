Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUPPORT_SUPPORT_term_abbrevs.
Require Import EXTENSION_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm585_spec.
Require Import thm586_spec.
Lemma lem5718210 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5718211 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem5718212 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem5718211 A s) (@lem5718210 A s)). Qed.
Lemma lem5718213 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem5718212 A s t). Qed.
Lemma lem5718214 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = ((s = t) = (term3 A s t)).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem5718240 {_83095 : Type'} : term4 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem5718241 {_83095 : Type'} (p : _83095 -> Prop) : term5 _83095 p.
Proof. exact (@lem5718240 _83095 p). Qed.
Lemma lem5718242 {_83095 : Type'} (p : _83095 -> Prop) : (term5 _83095 p) = (term6 _83095 p).
Proof. exact (eq_refl (term5 _83095 p)). Qed.
Lemma lem5718243 {_83095 : Type'} (p : _83095 -> Prop) : term6 _83095 p.
Proof. exact (EQ_MP (@lem5718242 _83095 p) (@lem5718241 _83095 p)). Qed.
Lemma lem5718244 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term7 _83095 p x.
Proof. exact (@lem5718243 _83095 p x). Qed.
Lemma lem5718245 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 p x) = ((term8 _83095 x p) = (p x)).
Proof. exact (eq_refl (term7 _83095 p x)). Qed.
Lemma lem5718254 {A B : Type'} (s : A -> Prop) : term9 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem5718255 {A B : Type'} (s : A -> Prop) : (term9 A B s) = (term10 A B s).
Proof. exact (eq_refl (term9 A B s)). Qed.
Lemma lem5718256 {A B : Type'} (s : A -> Prop) : term10 A B s.
Proof. exact (EQ_MP (@lem5718255 A B s) (@lem5718254 A B s)). Qed.
Lemma lem5718257 {A B : Type'} (s : A -> Prop) (f : A -> B) : term11 A B s f.
Proof. exact (@lem5718256 A B s f). Qed.
Lemma lem5718258 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term11 A B s f) = (term12 A B s f).
Proof. exact (eq_refl (term11 A B s f)). Qed.
Lemma lem5718259 {A B : Type'} (s : A -> Prop) (f : A -> B) : term12 A B s f.
Proof. exact (EQ_MP (@lem5718258 A B s f) (@lem5718257 A B s f)). Qed.
Lemma lem5718260 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term13 A B s f op.
Proof. exact (@lem5718259 A B s f op). Qed.
Lemma lem5718261 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term13 A B s f op) = ((@support A B op f s) = (term14 A B s f op)).
Proof. exact (eq_refl (term13 A B s f op)). Qed.
Lemma lem5718278 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term3 A s t).
Proof. exact (EQ_MP (@lem5718214 A s t) (@lem5718213 A s t)). Qed.
Lemma lem5718279 {_119862 : Type'} (s : _119862 -> Prop) (t : _119862 -> Prop) : (s = t) = (term3 _119862 s t).
Proof. exact (@lem5718278 _119862 s t). Qed.
Lemma lem5718280 {_119851 _119862 : Type'} (op : type1400 _119851) (f : _119862 -> _119851) (s : _119862 -> Prop) : ((term15 _119851 _119862 op f s) = (@support _119862 _119851 op f s)) = (term16 _119851 _119862 op f s).
Proof. exact (@lem5718279 _119862 (term15 _119851 _119862 op f s) (@support _119862 _119851 op f s)). Qed.
Lemma lem5718290 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term14 A B s f op).
Proof. exact (EQ_MP (@lem5718261 A B s f op) (@lem5718260 A B s f op)). Qed.
Lemma lem5718291 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (@support _119862 _119851 op f s) = (term17 _119851 _119862 s f op).
Proof. exact (@lem5718290 _119862 _119851 s f op). Qed.
Lemma lem5718292 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term15 _119851 _119862 op f s) = (term18 _119851 _119862 s f op).
Proof. exact (@lem5718291 _119851 _119862 (@support _119862 _119851 op f s) f op). Qed.
Lemma lem5718300 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term14 A B s f op).
Proof. exact (EQ_MP (@lem5718261 A B s f op) (@lem5718260 A B s f op)). Qed.
Lemma lem5718301 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (@support _119862 _119851 op f s) = (term17 _119851 _119862 s f op).
Proof. exact (@lem5718300 _119862 _119851 s f op). Qed.
Lemma lem5718312 {_119862 : Type'} (x : _119862) : (@IN _119862 x) = (@IN _119862 x).
Proof. exact (eq_refl (@IN _119862 x)). Qed.
Lemma lem5718313 {_119851 _119862 : Type'} (x : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term19 _119851 _119862 x op f s) = (term20 _119851 _119862 x s f op).
Proof. exact (MK_COMB (@lem5718312 _119862 x) (@lem5718301 _119851 _119862 s f op)). Qed.
Lemma lem5718315 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5718245 _83095 p x) (@lem5718244 _83095 p x)). Qed.
Lemma lem5718316 {_119862 : Type'} (p : _119862 -> Prop) (x : _119862) : (term8 _119862 x p) = (p x).
Proof. exact (@lem5718315 _119862 p x). Qed.
Lemma lem5718317 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) (x : _119862) : (term21 _119851 _119862 x s f op) = (term22 _119851 _119862 s f op x).
Proof. exact (@lem5718316 _119862 (term23 _119851 _119862 s f op) x). Qed.
Lemma lem5718318 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term22 _119851 _119862 s f op x) = (term24 _119851 _119862 s f x op).
Proof. exact (eq_refl (term22 _119851 _119862 s f op x)). Qed.
Lemma lem5718319 {_119862 : Type'} (GEN_PVAR_237 : _119862) : (@SETSPEC _119862 GEN_PVAR_237) = (@SETSPEC _119862 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _119862 GEN_PVAR_237)). Qed.
Lemma lem5718320 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term25 _119851 _119862 GEN_PVAR_237 s f op x) = (term26 _119851 _119862 GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem5718319 _119862 GEN_PVAR_237) (@lem5718318 _119851 _119862 s f x op)). Qed.
Lemma lem5718321 {_119862 : Type'} (x : _119862) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5718322 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) (x : _119862) : (term27 _119851 _119862 GEN_PVAR_237 s f op x) = (term28 _119851 _119862 GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem5718320 _119851 _119862 GEN_PVAR_237 s f x op) (@lem5718321 _119862 x)). Qed.
Lemma lem5718323 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term29 _119851 _119862 GEN_PVAR_237 s f op) = (term30 _119851 _119862 GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : _119862 => @lem5718322 _119851 _119862 GEN_PVAR_237 s f op x)). Qed.
Lemma lem5718324 {_119862 : Type'} : (@ex _119862) = (@ex _119862).
Proof. exact (eq_refl (@ex _119862)). Qed.
Lemma lem5718325 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term31 _119851 _119862 GEN_PVAR_237 s f op) = (term32 _119851 _119862 GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem5718324 _119862) (@lem5718323 _119851 _119862 GEN_PVAR_237 s f op)). Qed.
Lemma lem5718326 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term33 _119851 _119862 s f op) = (term34 _119851 _119862 s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _119862 => @lem5718325 _119851 _119862 GEN_PVAR_237 s f op)). Qed.
Lemma lem5718327 {_119862 : Type'} : (@GSPEC _119862) = (@GSPEC _119862).
Proof. exact (eq_refl (@GSPEC _119862)). Qed.
Lemma lem5718328 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term35 _119851 _119862 s f op) = (term17 _119851 _119862 s f op).
Proof. exact (MK_COMB (@lem5718327 _119862) (@lem5718326 _119851 _119862 s f op)). Qed.
Lemma lem5718329 {_119862 : Type'} (x : _119862) : (@IN _119862 x) = (@IN _119862 x).
Proof. exact (eq_refl (@IN _119862 x)). Qed.
Lemma lem5718330 {_119851 _119862 : Type'} (x : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term21 _119851 _119862 x s f op) = (term20 _119851 _119862 x s f op).
Proof. exact (MK_COMB (@lem5718329 _119862 x) (@lem5718328 _119851 _119862 s f op)). Qed.
Lemma lem5718331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5718332 {_119851 _119862 : Type'} (x : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term36 _119851 _119862 x s f op) = (term37 _119851 _119862 x s f op).
Proof. exact (MK_COMB (@lem5718331) (@lem5718330 _119851 _119862 x s f op)). Qed.
Lemma lem5718333 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term22 _119851 _119862 s f op x) = (term24 _119851 _119862 s f x op).
Proof. exact (eq_refl (term22 _119851 _119862 s f op x)). Qed.
Lemma lem5718334 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : ((term21 _119851 _119862 x s f op) = (term22 _119851 _119862 s f op x)) = ((term20 _119851 _119862 x s f op) = (term24 _119851 _119862 s f x op)).
Proof. exact (MK_COMB (@lem5718332 _119851 _119862 x s f op) (@lem5718333 _119851 _119862 s f x op)). Qed.
Lemma lem5718335 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term20 _119851 _119862 x s f op) = (term24 _119851 _119862 s f x op).
Proof. exact (EQ_MP (@lem5718334 _119851 _119862 s f x op) (@lem5718317 _119851 _119862 s f op x)). Qed.
Lemma lem5718342 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term19 _119851 _119862 x op f s) = (term24 _119851 _119862 s f x op).
Proof. exact (TRANS (@lem5718313 _119851 _119862 x s f op) (@lem5718335 _119851 _119862 s f x op)). Qed.
Lemma lem5718343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5718344 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term38 _119851 _119862 x op f s) = (term39 _119851 _119862 s f x op).
Proof. exact (MK_COMB (@lem5718343) (@lem5718342 _119851 _119862 s f x op)). Qed.
Lemma lem5718349 {_119851 _119862 : Type'} (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term40 _119851 _119862 f x op) = (term40 _119851 _119862 f x op).
Proof. exact (eq_refl (term40 _119851 _119862 f x op)). Qed.
Lemma lem5718350 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term41 _119851 _119862 s f x op) = (term42 _119851 _119862 s f x op).
Proof. exact (MK_COMB (@lem5718344 _119851 _119862 s f x op) (@lem5718349 _119851 _119862 f x op)). Qed.
Lemma lem5718353 {_119862 : Type'} (GEN_PVAR_237 : _119862) : (@SETSPEC _119862 GEN_PVAR_237) = (@SETSPEC _119862 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _119862 GEN_PVAR_237)). Qed.
Lemma lem5718354 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term43 _119851 _119862 GEN_PVAR_237 s f x op) = (term44 _119851 _119862 GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem5718353 _119862 GEN_PVAR_237) (@lem5718350 _119851 _119862 s f x op)). Qed.
Lemma lem5718355 {_119862 : Type'} (x : _119862) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5718356 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) (x : _119862) : (term45 _119851 _119862 GEN_PVAR_237 s f op x) = (term46 _119851 _119862 GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem5718354 _119851 _119862 GEN_PVAR_237 s f x op) (@lem5718355 _119862 x)). Qed.
Lemma lem5718357 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term47 _119851 _119862 GEN_PVAR_237 s f op) = (term48 _119851 _119862 GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : _119862 => @lem5718356 _119851 _119862 GEN_PVAR_237 s f op x)). Qed.
Lemma lem5718358 {_119862 : Type'} : (@ex _119862) = (@ex _119862).
Proof. exact (eq_refl (@ex _119862)). Qed.
Lemma lem5718359 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term49 _119851 _119862 GEN_PVAR_237 s f op) = (term50 _119851 _119862 GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem5718358 _119862) (@lem5718357 _119851 _119862 GEN_PVAR_237 s f op)). Qed.
Lemma lem5718364 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term51 _119851 _119862 s f op) = (term52 _119851 _119862 s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _119862 => @lem5718359 _119851 _119862 GEN_PVAR_237 s f op)). Qed.
Lemma lem5718365 {_119862 : Type'} : (@GSPEC _119862) = (@GSPEC _119862).
Proof. exact (eq_refl (@GSPEC _119862)). Qed.
Lemma lem5718366 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term18 _119851 _119862 s f op) = (term53 _119851 _119862 s f op).
Proof. exact (MK_COMB (@lem5718365 _119862) (@lem5718364 _119851 _119862 s f op)). Qed.
Lemma lem5718367 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term15 _119851 _119862 op f s) = (term53 _119851 _119862 s f op).
Proof. exact (TRANS (@lem5718292 _119851 _119862 s f op) (@lem5718366 _119851 _119862 s f op)). Qed.
Lemma lem5718368 {_119862 : Type'} (x : _119862) : (@IN _119862 x) = (@IN _119862 x).
Proof. exact (eq_refl (@IN _119862 x)). Qed.
Lemma lem5718369 {_119851 _119862 : Type'} (x : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term54 _119851 _119862 x op f s) = (term55 _119851 _119862 x s f op).
Proof. exact (MK_COMB (@lem5718368 _119862 x) (@lem5718367 _119851 _119862 s f op)). Qed.
Lemma lem5718371 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5718245 _83095 p x) (@lem5718244 _83095 p x)). Qed.
Lemma lem5718372 {_119862 : Type'} (p : _119862 -> Prop) (x : _119862) : (term8 _119862 x p) = (p x).
Proof. exact (@lem5718371 _119862 p x). Qed.
Lemma lem5718373 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) (x : _119862) : (term56 _119851 _119862 x s f op) = (term57 _119851 _119862 s f op x).
Proof. exact (@lem5718372 _119862 (term58 _119851 _119862 s f op) x). Qed.
Lemma lem5718374 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term57 _119851 _119862 s f op x) = (term42 _119851 _119862 s f x op).
Proof. exact (eq_refl (term57 _119851 _119862 s f op x)). Qed.
Lemma lem5718375 {_119862 : Type'} (GEN_PVAR_237 : _119862) : (@SETSPEC _119862 GEN_PVAR_237) = (@SETSPEC _119862 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _119862 GEN_PVAR_237)). Qed.
Lemma lem5718376 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term59 _119851 _119862 GEN_PVAR_237 s f op x) = (term44 _119851 _119862 GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem5718375 _119862 GEN_PVAR_237) (@lem5718374 _119851 _119862 s f x op)). Qed.
Lemma lem5718377 {_119862 : Type'} (x : _119862) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5718378 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) (x : _119862) : (term60 _119851 _119862 GEN_PVAR_237 s f op x) = (term46 _119851 _119862 GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem5718376 _119851 _119862 GEN_PVAR_237 s f x op) (@lem5718377 _119862 x)). Qed.
Lemma lem5718379 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term61 _119851 _119862 GEN_PVAR_237 s f op) = (term48 _119851 _119862 GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : _119862 => @lem5718378 _119851 _119862 GEN_PVAR_237 s f op x)). Qed.
Lemma lem5718380 {_119862 : Type'} : (@ex _119862) = (@ex _119862).
Proof. exact (eq_refl (@ex _119862)). Qed.
Lemma lem5718381 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term62 _119851 _119862 GEN_PVAR_237 s f op) = (term50 _119851 _119862 GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem5718380 _119862) (@lem5718379 _119851 _119862 GEN_PVAR_237 s f op)). Qed.
Lemma lem5718382 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term63 _119851 _119862 s f op) = (term52 _119851 _119862 s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _119862 => @lem5718381 _119851 _119862 GEN_PVAR_237 s f op)). Qed.
Lemma lem5718383 {_119862 : Type'} : (@GSPEC _119862) = (@GSPEC _119862).
Proof. exact (eq_refl (@GSPEC _119862)). Qed.
Lemma lem5718384 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term64 _119851 _119862 s f op) = (term53 _119851 _119862 s f op).
Proof. exact (MK_COMB (@lem5718383 _119862) (@lem5718382 _119851 _119862 s f op)). Qed.
Lemma lem5718385 {_119862 : Type'} (x : _119862) : (@IN _119862 x) = (@IN _119862 x).
Proof. exact (eq_refl (@IN _119862 x)). Qed.
Lemma lem5718386 {_119851 _119862 : Type'} (x : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term56 _119851 _119862 x s f op) = (term55 _119851 _119862 x s f op).
Proof. exact (MK_COMB (@lem5718385 _119862 x) (@lem5718384 _119851 _119862 s f op)). Qed.
Lemma lem5718387 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5718388 {_119851 _119862 : Type'} (x : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term65 _119851 _119862 x s f op) = (term66 _119851 _119862 x s f op).
Proof. exact (MK_COMB (@lem5718387) (@lem5718386 _119851 _119862 x s f op)). Qed.
Lemma lem5718389 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term57 _119851 _119862 s f op x) = (term42 _119851 _119862 s f x op).
Proof. exact (eq_refl (term57 _119851 _119862 s f op x)). Qed.
Lemma lem5718390 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : ((term56 _119851 _119862 x s f op) = (term57 _119851 _119862 s f op x)) = ((term55 _119851 _119862 x s f op) = (term42 _119851 _119862 s f x op)).
Proof. exact (MK_COMB (@lem5718388 _119851 _119862 x s f op) (@lem5718389 _119851 _119862 s f x op)). Qed.
Lemma lem5718391 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term55 _119851 _119862 x s f op) = (term42 _119851 _119862 s f x op).
Proof. exact (EQ_MP (@lem5718390 _119851 _119862 s f x op) (@lem5718373 _119851 _119862 s f op x)). Qed.
Lemma lem5718404 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term54 _119851 _119862 x op f s) = (term42 _119851 _119862 s f x op).
Proof. exact (TRANS (@lem5718369 _119851 _119862 x s f op) (@lem5718391 _119851 _119862 s f x op)). Qed.
Lemma lem5718405 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5718406 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term67 _119851 _119862 x op f s) = (term68 _119851 _119862 s f x op).
Proof. exact (MK_COMB (@lem5718405) (@lem5718404 _119851 _119862 s f x op)). Qed.
Lemma lem5718408 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term14 A B s f op).
Proof. exact (EQ_MP (@lem5718261 A B s f op) (@lem5718260 A B s f op)). Qed.
Lemma lem5718409 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (@support _119862 _119851 op f s) = (term17 _119851 _119862 s f op).
Proof. exact (@lem5718408 _119862 _119851 s f op). Qed.
Lemma lem5718420 {_119862 : Type'} (x : _119862) : (@IN _119862 x) = (@IN _119862 x).
Proof. exact (eq_refl (@IN _119862 x)). Qed.
Lemma lem5718421 {_119851 _119862 : Type'} (x : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term19 _119851 _119862 x op f s) = (term20 _119851 _119862 x s f op).
Proof. exact (MK_COMB (@lem5718420 _119862 x) (@lem5718409 _119851 _119862 s f op)). Qed.
Lemma lem5718423 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem5718245 _83095 p x) (@lem5718244 _83095 p x)). Qed.
Lemma lem5718424 {_119862 : Type'} (p : _119862 -> Prop) (x : _119862) : (term8 _119862 x p) = (p x).
Proof. exact (@lem5718423 _119862 p x). Qed.
Lemma lem5718425 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) (x : _119862) : (term21 _119851 _119862 x s f op) = (term22 _119851 _119862 s f op x).
Proof. exact (@lem5718424 _119862 (term23 _119851 _119862 s f op) x). Qed.
Lemma lem5718426 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term22 _119851 _119862 s f op x) = (term24 _119851 _119862 s f x op).
Proof. exact (eq_refl (term22 _119851 _119862 s f op x)). Qed.
Lemma lem5718427 {_119862 : Type'} (GEN_PVAR_237 : _119862) : (@SETSPEC _119862 GEN_PVAR_237) = (@SETSPEC _119862 GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC _119862 GEN_PVAR_237)). Qed.
Lemma lem5718428 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term25 _119851 _119862 GEN_PVAR_237 s f op x) = (term26 _119851 _119862 GEN_PVAR_237 s f x op).
Proof. exact (MK_COMB (@lem5718427 _119862 GEN_PVAR_237) (@lem5718426 _119851 _119862 s f x op)). Qed.
Lemma lem5718429 {_119862 : Type'} (x : _119862) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5718430 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) (x : _119862) : (term27 _119851 _119862 GEN_PVAR_237 s f op x) = (term28 _119851 _119862 GEN_PVAR_237 s f op x).
Proof. exact (MK_COMB (@lem5718428 _119851 _119862 GEN_PVAR_237 s f x op) (@lem5718429 _119862 x)). Qed.
Lemma lem5718431 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term29 _119851 _119862 GEN_PVAR_237 s f op) = (term30 _119851 _119862 GEN_PVAR_237 s f op).
Proof. exact (fun_ext (fun x : _119862 => @lem5718430 _119851 _119862 GEN_PVAR_237 s f op x)). Qed.
Lemma lem5718432 {_119862 : Type'} : (@ex _119862) = (@ex _119862).
Proof. exact (eq_refl (@ex _119862)). Qed.
Lemma lem5718433 {_119851 _119862 : Type'} (GEN_PVAR_237 : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term31 _119851 _119862 GEN_PVAR_237 s f op) = (term32 _119851 _119862 GEN_PVAR_237 s f op).
Proof. exact (MK_COMB (@lem5718432 _119862) (@lem5718431 _119851 _119862 GEN_PVAR_237 s f op)). Qed.
Lemma lem5718434 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term33 _119851 _119862 s f op) = (term34 _119851 _119862 s f op).
Proof. exact (fun_ext (fun GEN_PVAR_237 : _119862 => @lem5718433 _119851 _119862 GEN_PVAR_237 s f op)). Qed.
Lemma lem5718435 {_119862 : Type'} : (@GSPEC _119862) = (@GSPEC _119862).
Proof. exact (eq_refl (@GSPEC _119862)). Qed.
Lemma lem5718436 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term35 _119851 _119862 s f op) = (term17 _119851 _119862 s f op).
Proof. exact (MK_COMB (@lem5718435 _119862) (@lem5718434 _119851 _119862 s f op)). Qed.
Lemma lem5718437 {_119862 : Type'} (x : _119862) : (@IN _119862 x) = (@IN _119862 x).
Proof. exact (eq_refl (@IN _119862 x)). Qed.
Lemma lem5718438 {_119851 _119862 : Type'} (x : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term21 _119851 _119862 x s f op) = (term20 _119851 _119862 x s f op).
Proof. exact (MK_COMB (@lem5718437 _119862 x) (@lem5718436 _119851 _119862 s f op)). Qed.
Lemma lem5718439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5718440 {_119851 _119862 : Type'} (x : _119862) (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term36 _119851 _119862 x s f op) = (term37 _119851 _119862 x s f op).
Proof. exact (MK_COMB (@lem5718439) (@lem5718438 _119851 _119862 x s f op)). Qed.
Lemma lem5718441 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term22 _119851 _119862 s f op x) = (term24 _119851 _119862 s f x op).
Proof. exact (eq_refl (term22 _119851 _119862 s f op x)). Qed.
Lemma lem5718442 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : ((term21 _119851 _119862 x s f op) = (term22 _119851 _119862 s f op x)) = ((term20 _119851 _119862 x s f op) = (term24 _119851 _119862 s f x op)).
Proof. exact (MK_COMB (@lem5718440 _119851 _119862 x s f op) (@lem5718441 _119851 _119862 s f x op)). Qed.
Lemma lem5718443 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term20 _119851 _119862 x s f op) = (term24 _119851 _119862 s f x op).
Proof. exact (EQ_MP (@lem5718442 _119851 _119862 s f x op) (@lem5718425 _119851 _119862 s f op x)). Qed.
Lemma lem5718450 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term19 _119851 _119862 x op f s) = (term24 _119851 _119862 s f x op).
Proof. exact (TRANS (@lem5718421 _119851 _119862 x s f op) (@lem5718443 _119851 _119862 s f x op)). Qed.
Lemma lem5718451 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : ((term54 _119851 _119862 x op f s) = (term19 _119851 _119862 x op f s)) = ((term42 _119851 _119862 s f x op) = (term24 _119851 _119862 s f x op)).
Proof. exact (MK_COMB (@lem5718406 _119851 _119862 s f x op) (@lem5718450 _119851 _119862 s f x op)). Qed.
Lemma lem5718456 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term69 _119851 _119862 op f s) = (term70 _119851 _119862 s f op).
Proof. exact (fun_ext (fun x : _119862 => @lem5718451 _119851 _119862 s f x op)). Qed.
Lemma lem5718457 {_119862 : Type'} : (@all _119862) = (@all _119862).
Proof. exact (eq_refl (@all _119862)). Qed.
Lemma lem5718458 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term16 _119851 _119862 op f s) = (term71 _119851 _119862 s f op).
Proof. exact (MK_COMB (@lem5718457 _119862) (@lem5718456 _119851 _119862 s f op)). Qed.
Lemma lem5718463 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : ((term15 _119851 _119862 op f s) = (@support _119862 _119851 op f s)) = (term71 _119851 _119862 s f op).
Proof. exact (TRANS (@lem5718280 _119851 _119862 op f s) (@lem5718458 _119851 _119862 s f op)). Qed.
Lemma lem5718464 {_119851 _119862 : Type'} (f : _119862 -> _119851) (op : type1400 _119851) : (term72 _119851 _119862 op f) = (term73 _119851 _119862 f op).
Proof. exact (fun_ext (fun s : _119862 -> Prop => @lem5718463 _119851 _119862 s f op)). Qed.
Lemma lem5718465 {_119862 : Type'} : (@all (_119862 -> Prop)) = (@all (_119862 -> Prop)).
Proof. exact (eq_refl (@all (_119862 -> Prop))). Qed.
Lemma lem5718466 {_119851 _119862 : Type'} (f : _119862 -> _119851) (op : type1400 _119851) : (term74 _119851 _119862 op f) = (term75 _119851 _119862 f op).
Proof. exact (MK_COMB (@lem5718465 _119862) (@lem5718464 _119851 _119862 f op)). Qed.
Lemma lem5718471 {_119851 _119862 : Type'} (op : type1400 _119851) : (term76 _119851 _119862 op) = (term77 _119851 _119862 op).
Proof. exact (fun_ext (fun f : _119862 -> _119851 => @lem5718466 _119851 _119862 f op)). Qed.
Lemma lem5718472 {_119851 _119862 : Type'} : (@all (_119862 -> _119851)) = (@all (_119862 -> _119851)).
Proof. exact (eq_refl (@all (_119862 -> _119851))). Qed.
Lemma lem5718473 {_119851 _119862 : Type'} (op : type1400 _119851) : (term78 _119851 _119862 op) = (term79 _119851 _119862 op).
Proof. exact (MK_COMB (@lem5718472 _119851 _119862) (@lem5718471 _119851 _119862 op)). Qed.
Lemma lem5718478 {_119851 _119862 : Type'} : (term80 _119851 _119862) = (term81 _119851 _119862).
Proof. exact (fun_ext (fun op : type1400 _119851 => @lem5718473 _119851 _119862 op)). Qed.
Lemma lem5718479 {_119851 : Type'} : (@all (_119851 -> _119851 -> _119851)) = (@all (_119851 -> _119851 -> _119851)).
Proof. exact (eq_refl (@all (_119851 -> _119851 -> _119851))). Qed.
Lemma lem5718480 {_119851 _119862 : Type'} : (term82 _119851 _119862) = (term83 _119851 _119862).
Proof. exact (MK_COMB (@lem5718479 _119851) (@lem5718478 _119851 _119862)). Qed.
Lemma lem5718485 {_119851 _119862 : Type'} : (term83 _119851 _119862) = (term82 _119851 _119862).
Proof. exact (SYM (@lem5718480 _119851 _119862)). Qed.
Lemma lem5718505 (p : Prop) (q : Prop) (r : Prop) : (term84 p q r) = (term85 p q r).
Proof. exact (EQ_MP (@lem586 p q r) (@lem585 p q r)). Qed.
Lemma lem5718506 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term42 _119851 _119862 s f x op) = (term86 _119851 _119862 s f x op).
Proof. exact (@lem5718505 (@IN _119862 x s) (term40 _119851 _119862 f x op) (term40 _119851 _119862 f x op)). Qed.
Lemma lem5718520 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem5718521 {_119851 _119862 : Type'} (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term87 _119851 _119862 f x op) = (term40 _119851 _119862 f x op).
Proof. exact (@lem5718520 (term40 _119851 _119862 f x op)). Qed.
Lemma lem5718524 {_119862 : Type'} (x : _119862) (s : _119862 -> Prop) : (term88 _119862 x s) = (term88 _119862 x s).
Proof. exact (eq_refl (term88 _119862 x s)). Qed.
Lemma lem5718525 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term86 _119851 _119862 s f x op) = (term24 _119851 _119862 s f x op).
Proof. exact (MK_COMB (@lem5718524 _119862 x s) (@lem5718521 _119851 _119862 f x op)). Qed.
Lemma lem5718533 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term42 _119851 _119862 s f x op) = (term24 _119851 _119862 s f x op).
Proof. exact (TRANS (@lem5718506 _119851 _119862 s f x op) (@lem5718525 _119851 _119862 s f x op)). Qed.
Lemma lem5718534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5718535 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term68 _119851 _119862 s f x op) = (term89 _119851 _119862 s f x op).
Proof. exact (MK_COMB (@lem5718534) (@lem5718533 _119851 _119862 s f x op)). Qed.
Lemma lem5718545 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : (term24 _119851 _119862 s f x op) = (term24 _119851 _119862 s f x op).
Proof. exact (eq_refl (term24 _119851 _119862 s f x op)). Qed.
Lemma lem5718546 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : ((term42 _119851 _119862 s f x op) = (term24 _119851 _119862 s f x op)) = ((term24 _119851 _119862 s f x op) = (term24 _119851 _119862 s f x op)).
Proof. exact (MK_COMB (@lem5718535 _119851 _119862 s f x op) (@lem5718545 _119851 _119862 s f x op)). Qed.
Lemma lem5718548 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5718549 (x : Prop) : (x = x) = True.
Proof. exact (@lem5718548 Prop x). Qed.
Lemma lem5718550 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : ((term24 _119851 _119862 s f x op) = (term24 _119851 _119862 s f x op)) = True.
Proof. exact (@lem5718549 (term24 _119851 _119862 s f x op)). Qed.
Lemma lem5718551 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (x : _119862) (op : type1400 _119851) : ((term42 _119851 _119862 s f x op) = (term24 _119851 _119862 s f x op)) = True.
Proof. exact (TRANS (@lem5718546 _119851 _119862 s f x op) (@lem5718550 _119851 _119862 s f x op)). Qed.
Lemma lem5718552 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term70 _119851 _119862 s f op) = (term90 _119862).
Proof. exact (fun_ext (fun x : _119862 => @lem5718551 _119851 _119862 s f x op)). Qed.
Lemma lem5718553 {_119862 : Type'} : (@all _119862) = (@all _119862).
Proof. exact (eq_refl (@all _119862)). Qed.
Lemma lem5718554 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term71 _119851 _119862 s f op) = (term91 _119862).
Proof. exact (MK_COMB (@lem5718553 _119862) (@lem5718552 _119851 _119862 s f op)). Qed.
Lemma lem5718556 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5718557 {_119862 : Type'} (t : Prop) : (term92 _119862 t) = t.
Proof. exact (@lem5718556 _119862 t). Qed.
Lemma lem5718558 {_119862 : Type'} : (term91 _119862) = True.
Proof. exact (@lem5718557 _119862 True). Qed.
Lemma lem5718559 {_119851 _119862 : Type'} (s : _119862 -> Prop) (f : _119862 -> _119851) (op : type1400 _119851) : (term71 _119851 _119862 s f op) = True.
Proof. exact (TRANS (@lem5718554 _119851 _119862 s f op) (@lem5718558 _119862)). Qed.
Lemma lem5718560 {_119851 _119862 : Type'} (f : _119862 -> _119851) (op : type1400 _119851) : (term73 _119851 _119862 f op) = (term93 _119862).
Proof. exact (fun_ext (fun s : _119862 -> Prop => @lem5718559 _119851 _119862 s f op)). Qed.
Lemma lem5718561 {_119862 : Type'} : (@all (_119862 -> Prop)) = (@all (_119862 -> Prop)).
Proof. exact (eq_refl (@all (_119862 -> Prop))). Qed.
Lemma lem5718562 {_119851 _119862 : Type'} (f : _119862 -> _119851) (op : type1400 _119851) : (term75 _119851 _119862 f op) = (term94 _119862).
Proof. exact (MK_COMB (@lem5718561 _119862) (@lem5718560 _119851 _119862 f op)). Qed.
Lemma lem5718564 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5718565 {_119862 : Type'} (t : Prop) : (term95 _119862 t) = t.
Proof. exact (@lem5718564 (_119862 -> Prop) t). Qed.
Lemma lem5718566 {_119862 : Type'} : (term94 _119862) = True.
Proof. exact (@lem5718565 _119862 True). Qed.
Lemma lem5718567 {_119851 _119862 : Type'} (f : _119862 -> _119851) (op : type1400 _119851) : (term75 _119851 _119862 f op) = True.
Proof. exact (TRANS (@lem5718562 _119851 _119862 f op) (@lem5718566 _119862)). Qed.
Lemma lem5718568 {_119851 _119862 : Type'} (op : type1400 _119851) : (term77 _119851 _119862 op) = (term96 _119851 _119862).
Proof. exact (fun_ext (fun f : _119862 -> _119851 => @lem5718567 _119851 _119862 f op)). Qed.
Lemma lem5718569 {_119851 _119862 : Type'} : (@all (_119862 -> _119851)) = (@all (_119862 -> _119851)).
Proof. exact (eq_refl (@all (_119862 -> _119851))). Qed.
Lemma lem5718570 {_119851 _119862 : Type'} (op : type1400 _119851) : (term79 _119851 _119862 op) = (term97 _119851 _119862).
Proof. exact (MK_COMB (@lem5718569 _119851 _119862) (@lem5718568 _119851 _119862 op)). Qed.
Lemma lem5718572 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5718573 {_119851 _119862 : Type'} (t : Prop) : (term98 _119851 _119862 t) = t.
Proof. exact (@lem5718572 (_119862 -> _119851) t). Qed.
Lemma lem5718574 {_119851 _119862 : Type'} : (term97 _119851 _119862) = True.
Proof. exact (@lem5718573 _119851 _119862 True). Qed.
Lemma lem5718575 {_119851 _119862 : Type'} (op : type1400 _119851) : (term79 _119851 _119862 op) = True.
Proof. exact (TRANS (@lem5718570 _119851 _119862 op) (@lem5718574 _119851 _119862)). Qed.
Lemma lem5718576 {_119851 _119862 : Type'} : (term81 _119851 _119862) = (term99 _119851).
Proof. exact (fun_ext (fun op : type1400 _119851 => @lem5718575 _119851 _119862 op)). Qed.
Lemma lem5718577 {_119851 : Type'} : (@all (_119851 -> _119851 -> _119851)) = (@all (_119851 -> _119851 -> _119851)).
Proof. exact (eq_refl (@all (_119851 -> _119851 -> _119851))). Qed.
Lemma lem5718578 {_119851 _119862 : Type'} : (term83 _119851 _119862) = (term100 _119851).
Proof. exact (MK_COMB (@lem5718577 _119851) (@lem5718576 _119851 _119862)). Qed.
Lemma lem5718580 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5718581 {_119851 : Type'} (t : Prop) : (term101 _119851 t) = t.
Proof. exact (@lem5718580 (type1400 _119851) t). Qed.
Lemma lem5718582 {_119851 : Type'} : (term100 _119851) = True.
Proof. exact (@lem5718581 _119851 True). Qed.
Lemma lem5718583 {_119851 _119862 : Type'} : (term83 _119851 _119862) = True.
Proof. exact (TRANS (@lem5718578 _119851 _119862) (@lem5718582 _119851)). Qed.
Lemma lem5718584 {_119851 _119862 : Type'} : True = (term83 _119851 _119862).
Proof. exact (SYM (@lem5718583 _119851 _119862)). Qed.
Lemma lem5718585 {_119851 _119862 : Type'} : term83 _119851 _119862.
Proof. exact (EQ_MP (@lem5718584 _119851 _119862) (@lem0)). Qed.
Lemma lem5718586 {_119851 _119862 : Type'} : term82 _119851 _119862.
Proof. exact (EQ_MP (@lem5718485 _119851 _119862) (@lem5718585 _119851 _119862)). Qed.
